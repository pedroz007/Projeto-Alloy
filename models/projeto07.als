open util/boolean

sig Armazem {
    drones: set Drone,
    pedidos: set Pedido}

abstract sig Drone {
    disponivel: one Bool
}

sig DroneComum extends Drone {
	// existem 3 drones comuns
	// capacidade 3
}

sig DroneEspecial extends Drone {
	// existem 2 drones especiais
  // capacidade 5
} 

abstract sig Status {}

sig Pendente extends Status {}
sig Enviando extends Status {}
sig Entregue extends Status {}

sig Livro {}
sig Cliente {
    pedidos: set Pedido,
    ehConveniado: one Bool // pode ser conveniado ou não
} 

sig Pedido {
	livros: some Livro,         // algum livro
	cliente: one Cliente,       // se comum, até 3 livros, senão até 5
	drone: one Drone,         // apenas um drone
	status: one Status   // se já tiver com pedido não pode fazer outro
}


fact QuantidadeDeDrones {
    #DroneComum = 3 // diz que so tem 3 drones comuns
    #DroneEspecial = 2 // diz que so tem 2 drones especiais
    all d: Drone | d in DroneComum + DroneEspecial
}

fact CapacidadePorCliente {
  all p: Pedido |
    (p.cliente.ehConveniado = True implies #p.livros <= 5) and
    (p.cliente.ehConveniado = False implies #p.livros <= 3)  // diz que se for conveniado tem limite de 5 livros, senão so 3
}

fact SeNaoEstaEntregandoDeveEstarNoArmazem { // diz que se p drone não tá entregando ele tá no armazém
  all d: Drone |
    (d.disponivel = False) iff (d in Armazem.drones)
}

fact SeUmDroneEstaEmUmPedidoOPedidoTemEsseDrone {
  // Se um pedido tem um drone, então esse drone está ocupado com esse pedido.
  all p: Pedido | some p.drone implies
    // p.drone está com status Enviando e não está listado no armazém
    (p.drone not in Armazem.drones) and p.status = Enviando

  // Se um drone tem entrega, então esse pedido deve apontar de volta para ele
  all d: Drone |
    // se d tem algum pedido, então existe um pedido p com p.drone = d
    (some p: Pedido | p.drone = d) implies (one p: Pedido | p.drone = d) // confirma a relação
}



