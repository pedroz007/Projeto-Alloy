open util/boolean

//
one sig Armazem {
    drones: set Drone,
    pedidos: set Pedido}

abstract sig Drone {
    disponivel: one Bool,
    capacidade: Int
}

sig DroneComum extends Drone {}
sig DroneEspecial extends Drone {}

abstract sig Status {}

sig Pendente extends Status {}
sig Enviando extends Status {}
sig Entregue extends Status {}

sig Livro {}
sig Cliente {
    ehConveniado: one Bool
} 

sig Pedido {
    livros: set Livro,          // conjunto de livros
    cliente: one Cliente,       
    drone: lone Drone,          // pode não ter drone se o pedido estiver pendente
    status: one Status          
}


fact QuantidadeDeDrones {
    #DroneComum = 3 // diz que so tem 3 drones comuns
    #DroneEspecial = 2 // diz que so tem 2 drones especiais
    all d: Drone | d in DroneComum + DroneEspecial
}

fact CapacidadeDosDrones {
    all d: DroneComum | d.capacidade = 3      // drones comuns: capacidade 3
    all d: DroneEspecial | d.capacidade = 5   // drones especiais: capacidade 5
}

fact LimitesDePedidos {
    all p: Pedido | some p.livros // todo pedido deve ter pelo menos 1 livro
    
    // Clientes NÃO conveniados: máximo 3 livros e só podem usar drones comuns
    all p: Pedido | 
        p.cliente.ehConveniado = False implies 
        (#p.livros <= 3 and (some p.drone implies p.drone in DroneComum))
    
    // Clientes conveniados: máximo 5 livros podem usar drones especiais ou comuns
    all p: Pedido | 
        p.cliente.ehConveniado = True implies #p.livros <= 5
    
    all p: Pedido | some p.drone implies #p.livros <= p.drone.capacidade
}

fact StatusDroneArmazem {
    // Drones estão no armazém apenas quando não estão fazendo entrega
    all d: Drone |
        d in Armazem.drones iff (no p: Pedido | p.drone = d and p.status = Enviando)
        
    // Drone disponível significa que não está feznedo entrega
    all d: Drone |
        d.disponivel = True iff (no p: Pedido | p.drone = d and p.status = Enviando)
}

fact AlocacaoDrones {
    // Pedidos pendentes não têm drone alocado
    all p: Pedido | p.status = Pendente implies no p.drone
    
    // Pedidos enviando ou entregues devem ter drone alocado
    all p: Pedido | (p.status = Enviando or p.status = Entregue) implies one p.drone
    
    // Cada drone pode estar alocado a no máximo um pedido ativo
    all d: Drone | lone p: Pedido | p.drone = d and p.status != Entregue
}

// Clientes não podem fazer novos pedidos se já têm entrega em andamento
fact RestricaoClientePedido {
    all c: Cliente |
        (some p: Pedido | p.cliente = c and p.status = Enviando) implies
        (no p2: Pedido | p2.cliente = c and p2.status = Pendente)
}


//Deve existir pelo menos um pedido no sistema
pred existePedido {
    some Pedido
}

// Deve existir pelo menos um cliente conveniado
pred existeClienteConveniado {
    some c: Cliente | c.ehConveniado = True
}

// Deve existir pelo menos um cliente não conveniado
pred existeClienteNaoConveniado {
    some c: Cliente | c.ehConveniado = False
}

// Deve existir um pedido válido de cliente conveniado de até 5 livros
pred pedidoConveniadoValido {
    some p: Pedido |
        p.cliente.ehConveniado = True and
        #p.livros <= 5
}

// Deve existir um pedido válido de cliente NÃO conveniado de até 3 livros
pred pedidoNaoConveniadoValido {
    some p: Pedido |
        p.cliente.ehConveniado = False and
        #p.livros <= 3
}

// Deve existir pelo menos um drone em entrega
pred droneEmEntrega {
    some p: Pedido | p.status = Enviando
}

// Deve existir pelo menos um drone disponível no armazém
pred droneNoArmazem {
    some d: Drone | d.disponivel = True and d in Armazem.drones
}

// Cliente conveniado usando drone especial
pred clienteConveniadoUsaDroneEspecial {
    some p: Pedido | 
        p.cliente.ehConveniado = True and 
        p.drone in DroneEspecial and
        #p.livros > 3
}

pred sistemaCompleto {
    some p1: Pedido | p1.status = Pendente
    some p2: Pedido | p2.status = Enviando  
    some p3: Pedido | p3.status = Entregue
}




run existePedido for 5

// Verifica a diferença entre clientes
run {existeClienteConveniado and existeClienteNaoConveniado} for 5

// Verifica pedidos válidos
run {pedidoConveniadoValido and pedidoNaoConveniadoValido} for 5

// Verifica funcionamento do sistema de drones
run {droneEmEntrega and droneNoArmazem} for 5

// Verifica o  drone especial por cliente conveniado
run clienteConveniadoUsaDroneEspecial for 5

// Verifica o sistema completo
run sistemaCompleto for 6




