abstract class Tipo
case class TyInt() extends Tipo { override def toString = "int" }
case class TyBool() extends Tipo { override def toString = "bool" }
case class TyUnit() extends Tipo { override def toString = "unit" }
case class TyFun (t1: Tipo, t2: Tipo) extends Tipo { override def toString = "(" + t1 + " -> " + t2 + ")" }
case class TyRef (t: Tipo) extends Tipo { override def toString = t.toString + " ref" }
case class TyReg (eltos: List[(String,Tipo)]) extends Tipo { 
  override def toString = {
    eltos.foldLeft("{")((s, e) => s + e._1 + ": " + e._2 + ", ").dropRight(2) + "}"
  }
  
  def folder(s: String, e: (String, Tipo)): String = s + e._1 + ": " + e._2 + ", "
} 
case class TyTop() extends Tipo { override def toString = "top" }

abstract class Oper
case class Sum() extends Oper { override def toString = "+" }
case class Prod() extends Oper { override def toString = "*" }
case class Dif() extends Oper { override def toString = "/=" }
case class Eq() extends Oper { override def toString = "==" }

abstract class Expr
case class N (n:Int) extends Expr { override def toString = n.toString }
case class B (b:Boolean) extends Expr { override def toString = b.toString }
case class BinOp (op: Oper, e1: Expr, e2: Expr) extends Expr { override def toString = e1.toString + op.toString + e2.toString } 
case class If (e1: Expr, e2: Expr, e3: Expr) extends Expr { override def toString = "if " + e1 + " then " + e2 + " else " + e3 + " fi" }
case class Asg (e1: Expr, e2: Expr) extends Expr { override def toString = e1.toString + " := " + e2 }
case class Deref (e: Expr) extends Expr { override def toString = "!" + e }
case class Ref (e: Expr) extends Expr { override def toString = "ref(" + e + ")" }
case class Skip() extends Expr { override def toString = "skip" }
case class Seq (e1: Expr, e2: Expr) extends Expr { override def toString = e1.toString + ";" + e2 }
case class W (e1: Expr, e2: Expr) extends Expr { override def toString = "while " + e1 + " do " + e2 + " done" }
case class Fun (x: String, t: Tipo, e: Expr) extends Expr { override def toString = "fn " + x + ": " + t + " => (" + e + ")" } 
case class App (e1 : Expr, e2: Expr) extends Expr { override def toString = "(" + e1 + " " + e2 + ")" }
case class Id (x: String) extends Expr { override def toString = x }
case class Let (x: String, t: Tipo, e1: Expr, e2: Expr) extends Expr { 
  override def toString = "let " + x + ": " + t + " = " + e1 + " in " + e2
} 
case class Reg (eltos: List[(String,Expr)]) extends Expr { 
  override def toString = eltos.foldLeft("{")((s, e) => s + e._1 + " = " + e._2 + ", ").dropRight(2) + "}"
}
case class Proj (lab: String, e: Expr) extends Expr { override def toString = "#" + lab + " " + e }

class L3 {
  var debug = false
  type Gamma = List[(String, Tipo)]
  def typecheck(gamma: Gamma, e: Expr): Option[Tipo] = { 
    if (debug) Console.println(gamma, e)
    e match {
    case N(_) => Some(TyInt())
    
    case B(_) => Some(TyBool())
    
    case BinOp(op, e1, e2) => op match {
      case Sum() => (typecheck(gamma, e1), typecheck(gamma, e2)) match {
        case (Some(TyInt()), Some(TyInt())) => Some(TyInt())
        case _ => None
      }

      case Prod() => (typecheck(gamma, e1), typecheck(gamma, e2)) match {
        case (Some(TyInt()), Some(TyInt())) => Some(TyInt())
        case _ => None
      }

      case Eq() => (typecheck(gamma, e1), typecheck(gamma, e2)) match {
        case (Some(TyInt()), Some(TyInt())) => Some(TyBool())
        case (Some(TyBool()), Some(TyBool())) => Some(TyBool())
        case _ => None
      }
      
      case Dif() => (typecheck(gamma, e1), typecheck(gamma, e2)) match {
        case (Some(TyInt()), Some(TyInt())) => Some(TyBool())
        case (Some(TyBool()), Some(TyBool())) => Some(TyBool())
        case _ => None
      }
    }
    
    case Skip() => Some(TyUnit())
    
    case Seq(e1, e2) => typecheck(gamma, e1) match {
      case Some(TyUnit()) => typecheck(gamma, e2)
      case _ => None
    }
    
    case W(e1, e2) => (typecheck(gamma, e1), typecheck(gamma, e2)) match {
      case (Some(TyBool()), Some(TyUnit())) => Some(TyUnit())
      case _ => None
    }
    
    case Ref(e) => Some(TyRef(typecheck(gamma, e).get))
    
    case Deref(e) => typecheck(gamma, e) match {
      case Some(TyRef(t)) => Some(t)
      case _ => None
    }
    
    case Reg(el) => {
      var eltos = el map (te => (te._1, typecheck(gamma, te._2).get))
      Some(TyReg(eltos))
    }
    
    case Fun(x, t, e) => {
      val tf = typecheck((x, t) :: gamma, e)
      if (tf == None) None else Some(TyFun(t, tf.get))
    }
    
    case App(e1, e2) => typecheck(gamma, e1) match {
      case Some(TyFun(t1, t2)) => {
        val t3 = typecheck(gamma, e2)
        if (t3 == None) None else if (subtype(t1, t3.get)) Some(t2) else None
      }
      case _ => None
    }
    
    case Id(x) => gammaType(gamma, x)
    
    case Proj(lab, e) => typecheck(gamma, e) match {
      case Some(TyReg(el)) => {
          val elf = (el filter (e => e._1 == lab))
          if (elf.length == 0) None else Some(elf(0)._2)
      }
      case _ => None
    }
    
    case If(e1, e2, e3) => if (typecheck(gamma, e1) != Some(TyBool())) None else join(typecheck(gamma, e2), typecheck(gamma, e3))
    
    case Asg(e1, e2) => if (isValue(gamma, e2)) Some(TyUnit()) else None
    
    case Let(x, t, e1, e2) => if (typecheck(gamma, e1) == Some(t)) typecheck((x, t) :: gamma, e2) else None 
  }
  }
  // Pode muito bem ser isValue(...) = true
  def isValue(gamma: Gamma, e: Expr) = typecheck(gamma, e) match {
    case Some(TyInt()) => true
    case Some(TyBool()) => true
    case Some(TyUnit()) => true
    case Some(TyFun(_, _)) => true
    case Some(TyRef(_)) => true
    case Some(TyReg(_)) => true
    case Some(TyTop()) => true
    case _ => false
    
  }
  
  // Converter para Option[Tipo]
  def gammaType(gamma: Gamma, name: String): Option[Tipo] = {
    val list = gamma.filter(e => e._1 == name)
    if (list.length == 0) None else Some(list(0)._2)
  }
  
//  def subtype(t1: Tipo, t2: Tipo): Boolean = (t1, t2) match {
//    case (_, TyTop()) => true
//    case (TyFun(t11, t12), TyFun(t21, t22)) => subtype(t11, t21) && subtype(t22, t12)
//    case (TyReg(eltos1), TyReg(eltos2)) => (eltos2 filter (t => eltos1 contains t)) == eltos1
//    case _ => t1 == t2
//  }
//  
  /**
   * @author Alan **************************************************************************************
   */
  def subtype(subt: Tipo, supert: Tipo): Boolean = (subt,supert) match {
  case (_, TyTop()) => true
  case (TyFun(s1, s2),TyFun(t1, t2)) => subtype(t1,s1) && subtype(s2,t2)
  case (TyReg(trs: List[(String,Tipo)]),TyReg(trt: List[(String,Tipo)])) => 
  trt.containsSlice(trs) //&& trt.forall(x => trs.exists( y => (x._1 == y._1) && subtype(y._2,x._2)))
  case _ => subt == supert
  }
  /**
   * ***************************************************************************************************
   */
  
  def join(t1: Option[Tipo], t2: Option[Tipo]): Option[Tipo] = (t1, t2) match {
    case (Some(TyReg(eltos1)), Some(TyReg(eltos2))) => {
      val jeltos = eltos2 filter (t => eltos1 contains t)
      if (jeltos.length == 0) Some(TyTop()) else Some(TyReg(jeltos))
    }
    case (Some(TyFun(t1, t2)), Some(TyFun(s1, s2))) => {
      val j1 = join(Some(t1), Some(s1))
      val j2 = join(Some(t2), Some(s2))
      if (j1 == None || j2 == None) None else Some(TyFun(j1.get, j2.get))
    }
    case (None, _) => None
    case (_, None) => None
    case _ => if (t1 == t2) t1 else Some(TyTop())
  }
}

object L3 {
  type Gamma = List[(String, Tipo)]
  
  def main(args: Array[String]) {
    // Algumas primitivas
    val tp = TyReg(List[(String, Tipo)](("p", TyInt())))
    val tqp = TyReg(List[(String, Tipo)](("p", TyInt()), ("q", TyInt())))
    val rqp = Reg(List[(String, Expr)](("q", N(3)), ("p", N(2))))
    val rp = Reg(List[(String, Expr)](("p", N(4))))
    val fnf = Fun("f", TyFun(tp, TyInt()), BinOp(Sum(), App(Id("f"), rqp), App(Id("f"), rp)))
    val tfnf = TyFun(TyFun(tp, TyInt()), TyInt())
    
    val tyb2b = TyFun(TyBool(), TyBool())
    
    val f1 = Fun("b1", TyBool(), Fun("b2", TyBool(), N(3)))
    val f2 = Fun("u1", TyUnit(), B(true))
    val f3 = Fun("y", TyFun(TyBool(), tyb2b), Fun("x", TyBool(), App(App(Id("y"), Id("x")), Id("x"))))
    val f4 = Fun("x", TyFun(TyInt(), TyBool()), Fun("y", TyFun(TyUnit(), TyBool()), Fun("z", TyInt(), 
      App(Id("y"), App(Id("x"), Id("z")))
    )))
    
    val eif = If(B(false),
          Reg(List[(String, Expr)](("r", B(true)), ("p", N(8)))), 
          Reg(List[(String, Expr)](("a", B(false)), ("g", Skip()))))
    
    val f = Fun("f", TyFun(TyInt(), TyInt()), App(Id("f"), Id("f")))
    
    val fsub1 = If(B(true), Fun("a", TyInt(), rqp), Fun("b", TyInt(), rp))
    val fsub2 = If(B(true), Fun("a", tp, N(1)), Fun("b", tqp, N(4)))
    val f5 = Fun("x", tp, Proj("p", Id("x")))
    // Testes
    val exprs = List[(Expr, Option[Tipo])] (
      (BinOp(Sum(), N(1), N(4)), Some(TyInt())),
      (BinOp(Eq(), N(5), N(5)), Some(TyBool())),
      (BinOp(Eq(), B(true), B(false)), Some(TyBool())),
      (BinOp(Dif(), N(3), N(6)), Some(TyBool())),
      (BinOp(Prod(), N(9), N(4)), Some(TyInt())),
      (Skip(), Some(TyUnit())),
      (Reg(List[(String, Expr)](("a", N(4)), ("b", B(true)))), Some(TyReg(List[(String, Tipo)](("a", TyInt()), ("b", TyBool()))))),
      (Reg(List[(String, Expr)](("reg", Reg(List[(String, Expr)](("a", Skip()), ("x", N(9))))))), 
        Some(TyReg(List[(String, Tipo)](("reg", TyReg(List[(String, Tipo)](("a", TyUnit()), ("x", TyInt())))))
      ))),
      (Fun("x", TyInt(), BinOp(Sum(), N(5), Id("x"))), Some(TyFun(TyInt(), TyInt()))),
      (App(Fun("x", TyInt(), BinOp(Sum(), N(5), Id("x"))),N(4)), Some(TyInt())),
      (Proj("a", Reg(List[(String, Expr)](("a", N(4)), ("b", B(true))))), Some(TyInt())),
      (Fun("x", TyReg(List[(String, Tipo)](("d", TyInt()))), Proj("d", Id("x"))), Some(TyFun(TyReg(List[(String, Tipo)](("d", TyInt()))), TyInt()))),
      (If(B(true), N(9), N(3)), Some(TyInt())),
      (If(B(true), N(9), B(false)), Some(TyTop())),
      (If(B(false),
          Reg(List[(String, Expr)](("a", B(true)), ("x", N(8)))), 
          Reg(List[(String, Expr)](("a", B(false)), ("g", Skip())))), 
          Some(TyReg(List[(String, Tipo)](("a", TyBool())))
      )),
      (Asg(Ref(N(9)), N(10)), Some(TyUnit())),
      (Let("x", TyInt(), N(10), BinOp(Prod(), N(8), Id("x"))), Some(TyInt())),
      (Fun("x", TyInt(), Fun("x", TyBool(), Id("x"))), Some(TyFun(TyInt(), TyFun(TyBool(), TyBool())))),
      (fnf, Some(tfnf)),
      (f1, Some(TyFun(TyBool(), TyFun(TyBool(), TyInt())))),
      (f2, Some(TyFun(TyUnit(), TyBool()))),
      (f, None),
      (Fun("z", TyUnit(), App(f1, App(f2, Id("z")))), Some(TyFun(TyUnit(), TyFun(TyBool(), TyInt())))),
      (f3, Some(TyFun(TyFun(TyBool(), tyb2b), tyb2b))),
      (f4, None),
      (eif, Some(TyTop())),
      (App(fnf, eif), None),
      (fsub1, Some(TyFun(TyInt(), tp))),
      (fsub2, Some(TyFun(tp, TyInt()))),
      (App(fsub2, App(fsub1, N(1))), Some(TyInt())),
      (f5, Some(TyFun(tp, TyInt())))
    )
    
    val gamma: List[(String, Tipo)] = List()
    
    val interpreter = new L3()
    //interpreter.debug = true
    var i = 0
    for (expr <- exprs) {
      i = i + 1
      try {
        val t = interpreter.typecheck(gamma, expr._1)
        Console print (i.toString() + " " + (if (t == expr._2) "(    pass) " else "(Not pass) "))
        Console print(expr._1 + ": " + (if (t == None) "None" else t.get.toString))
        Console println (if (t != expr._2) " expected " + expr._2 else "") 
      } catch {
        case e: MatchError => Console println (e, expr)
      }
    }
  }
}