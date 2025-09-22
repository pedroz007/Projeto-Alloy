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
one sig Pendente extends Status {}
one sig Enviando extends Status {}
one sig Entregue extends Status {}

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

fact QuantidadeDeDrones {
    #DroneComum = 3
    #DroneEspecial = 2
    all d: Drone | d in DroneComum + DroneEspecial
}

fact CapacidadePorCliente {
  all p: Pedido |
    (p.cliente.ehConveniado = True implies #p.livros <= 5) and
    (p.cliente.ehConveniado = False implies #p.livros <= 3)
}

fact SeNaoEstaEntregandoDeveEstarNoArmazem {
  all d: Drone |
    (d.disponivel = True) implies (d in Armazem.drones)
}

fact UmPedidoPorCliente {
    all c: Cliente |
        lone p: Pedido | p.cliente = c
}

fact UmPedidoPorDrone {
    all d: Drone |
        lone p: Pedido | p.drone = d
}

fact DroneDisponivelSemPedido {
    all d: Drone |
        d not in Pedido.drone implies d.disponivel = True 
}

fact DroneEspecialParaPedidosGrandes {
    all p: Pedido |
        #p.livros > 3 implies p.drone in DroneEspecial
}
 
fact ClienteSoPodePedirSeDroneDisponivel {
    all c: Cliente |
        some d: Drone | d.disponivel = True implies
        lone p: Pedido | p.cliente = c
}

fact PedidoEmEntregaNaoNoArmazem {
    all p: Pedido |
        p.status = Enviando implies p.drone not in Armazem.drones
}

fact PedidoMinimo {
    all p: Pedido |
        #p.livros >= 1
}

fact PedidosPendentesSemDrone {
    all p: Pedido | p.status = Pendente implies no p.drone
}

fact PedidosEmEnvioComDrone {
    all p: Pedido | (p.status = Enviando or p.status = Entregue) implies one p.drone
}

fact DronesComApenasUmPedido {
    all d: Drone | lone p: Pedido | p.drone = d and p.status != Entregue
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
