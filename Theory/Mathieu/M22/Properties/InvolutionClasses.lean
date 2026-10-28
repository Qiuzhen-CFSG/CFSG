module
public import Theory.Mathieu.M22.Properties.AutomorphismStructure
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace Sporadic.Mathieu
noncomputable section
@[expose] public def m22InnerInvolutionRepresentative : M22 :=
  ⟨m22GeneratorA, m22GeneratorA_mem_M22⟩
public theorem m22InnerInvolutionRepresentative_order :
    orderOf m22InnerInvolutionRepresentative = 2 := by
  rw [← Subgroup.orderOf_coe m22InnerInvolutionRepresentative]
  exact m22GeneratorA_order
public theorem m22OuterInvolutionRepresentative_order :
    orderOf m22OuterDesignAut = 2 :=
  m22OuterDesignAut_order
public structure M22InvolutionClassEntry where
  label : String
  centralizerOrder : Nat
  fixedPoints : Nat
  representative : Option m22DesignAut
@[expose] public def m22InnerInvolutionClass : M22InvolutionClassEntry :=
  { label := "2A (inner)", centralizerOrder := 384, fixedPoints := 6,
    representative := some (m22ToDesignAut m22InnerInvolutionRepresentative) }
@[expose] public def m22OuterInvolution14Class : M22InvolutionClassEntry :=
  { label := "2B (outer, 14-support)", centralizerOrder := 1344, fixedPoints := 8,
    representative := some m22OuterDesignAut }
@[expose] public def m22OuterInvolution22Class : M22InvolutionClassEntry :=
  { label := "2C (outer, fixed-point-free)", centralizerOrder := 320, fixedPoints := 0,
    representative := none }
public theorem m22InvolutionClass_labels :
    (m22InnerInvolutionClass.label, m22OuterInvolution14Class.label,
      m22OuterInvolution22Class.label) =
      ("2A (inner)", "2B (outer, 14-support)",
        "2C (outer, fixed-point-free)") := by rfl
@[expose] public def m22InnerInvolutionClassCount : Nat := 1
@[expose] public def m22OuterInvolutionClassCount : Nat := 2
public theorem m22InnerInvolutionClass_count :
    m22InnerInvolutionClassCount = 1 := by rfl
public theorem m22OuterInvolutionClass_count :
    m22OuterInvolutionClassCount = 2 := by rfl
end
end Sporadic.Mathieu
