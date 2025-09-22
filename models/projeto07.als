open util/boolean

// =========================
// ENTIDADES
// =========================

one sig Armazem {
    drones: set Drone,
    pedidos: set Pedido
}

abstract sig Drone {
    disponivel: one Bool,
}

sig DroneComum extends Drone {}
sig DroneEspecial extends Drone {}

abstract sig Status {}
sig Pendente extends Status {}
sig Enviando extends Status {}
sig Entregue extends Status {}

sig Livro {}

sig Cliente {
    pedidos: set Pedido,
    ehConveniado: one Bool
} 

sig Pedido {
    livros: some Livro,
    cliente: one Cliente,
    drone: one Drone,
    status: one Status
}

// =========================
// FACTS
// =========================

// 1. Quantidade de drones
fact QuantidadeDeDrones {
    #DroneComum = 3
    #DroneEspecial = 2
    all d: Drone | d in DroneComum + DroneEspecial
}

fact CapacidadePorCliente {
  all p: Pedido |
    (p.cliente.ehConveniado = True implies #p.livros <= 5) and
    (p.cliente.ehConveniado = False implies #p.livros <= 3)  // diz que se for conveniado tem limite de 5 livros, senão so 3
}

fact SeNaoEstaEntregandoDeveEstarNoArmazem { // diz que se p drone não tá entregando ele tá no armazém
  all d: Drone |
    (d.disponivel = True) implies (d in Armazem.drones)
}

// 5. Um pedido por cliente
fact UmPedidoPorCliente {
    all c: Cliente |
        lone p: Pedido | p.cliente = c
}

// 6. Um pedido por drone
fact UmPedidoPorDrone {
    all d: Drone |
        lone p: Pedido | p.drone = d
}

// 7. Pedidos de mais de 3 livros usam DroneEspecial
fact DroneEspecialParaPedidosGrandes {
    all p: Pedido |
        #p.livros > 3 implies p.drone in DroneEspecial
}

// 8. Cliente só pode fazer pedido se houver drone disponível
fact ClienteSoPodePedirSeDroneDisponivel {
    all c: Cliente |
        some d: Drone | d.disponivel = True implies
        lone p: Pedido | p.cliente = c
}

// 9. Pedido em andamento → drone não está no armazém
fact PedidoEmEntregaNaoNoArmazem {
    all p: Pedido |
        p.status = Enviando implies p.drone not in Armazem.drones
}

fact AlocacaoDrones {
    // Pedidos pendentes não têm drone alocado
    all p: Pedido | p.status = Pendente implies no p.drone
    
    // Pedidos enviando ou entregues devem ter drone alocado
    all p: Pedido | (p.status = Enviando or p.status = Entregue) implies one p.drone
    
    // Cada drone pode estar alocado a no máximo um pedido ativo
    all d: Drone | lone p: Pedido | p.drone = d and p.status != Entregue
}

// Um pedido tem apenas UM cliente ligado a ele
fact UmPedidoEhFeitoPorApenasUmCliente {
    all p: Pedido | 
        one c: Cliente | p.cliente = c and p in c.pedidos 
}

fact PedidoEhApontadoPorUmCliente {
    all p: Pedido |
        lone c: Cliente | p in c.pedidos
}

// assertion para verificar se um cliente tem apenas um pedido com status de Enviando por vez
assert nenhumClienteComMaisDeUmPedidoEnviando {
    all c: Cliente |
        let pedidosEnviando = c.pedidos & { p: Pedido | p.status = Enviando } |
        #pedidosEnviando <= 1
}

fact RelacaoArmazemComPedidos { //todos os pedidos existentes tem que estar no armazem
    Armazem.pedidos = Pedido
}

fact RelacaoArmazemComDrones { //armazem controla todos os drones
    Armazem.drones = Drone
}

fact DroneDisponineisEstaoNoArmazem { // Se o Drone esta disponivel, esta no armazem. Se esta no armazem, esta disponivel
    all d: Drone | (d in Armazem.drones) iff (d.disponivel = True)
}

// =========================
// PREDICADOS PARA TESTE
// =========================

pred existePedido {
    some Pedido
}

pred existeClienteConveniado {
    some c: Cliente | c.ehConveniado = True
}

pred existeClienteNaoConveniado {
    some c: Cliente | c.ehConveniado = False
}

pred pedidoConveniadoValido {
    some p: Pedido |
        p.cliente.ehConveniado = True and
        #p.livros <= 5
}

pred pedidoNaoConveniadoValido {
    some p: Pedido |
        p.cliente.ehConveniado = False and
        #p.livros <= 3
}

pred droneEmEntrega {
    some p: Pedido | p.status = Enviando
}

pred droneNoArmazem {
    some d: Drone | d.disponivel = True and d in Armazem.drones
}

// =========================
// RUNS
// =========================

run existePedido for 10
run existeClienteConveniado for 10
run existeClienteNaoConveniado for 10
run pedidoConveniadoValido for 10
run pedidoNaoConveniadoValido for 10
run droneEmEntrega for 10
run droneNoArmazem for 10

check nenhumClienteComMaisDeUmPedidoEnviando for 10



