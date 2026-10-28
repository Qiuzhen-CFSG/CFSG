module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelFixedSupplement
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelSylow
public import Theory.Representation.FirstCohomologyAutomorphism.FixedElement
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinaryInvolution

/-!
# The dimension-three kernel split in original 12.2.25

The literal fixed supplement gives T=(T∩L)C_T(I). Factoring an element
of U which moves V through this product supplies an involution in
L∩C_T(U) with nontrivial image in L/O₂(L). Every q∈C_T(V) can be twisted
by V into the elementary C_T(U), so its displacement automorphism fixes
that involution. The descended natural cocycle is principal by the
binary SL3 involution calculation, proving C_T(V)=V×C_T(L).

This constructs the original actions and quotient elements; no cocycle
model or indecomposable module is assumed. Source: Aschbacher--Smith,
original 12.2.25, printed p.805, using B.4.8(3)'s submodule convention.
The common-centralizers owner retains the Sylow-factor disjointness step;
final source assembly belongs to qt-d-12213-local-rigidity.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- An element of the elementary radical lying in L acts nontrivially on V.
This also supplies an involutory lift for the central-cover calculation. -/
theorem exists_component_radical_noncentral
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ l : L, (l : G) ∈ (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
      (l : G) ∉ centralizer (V : Set G) := by
  let := C.elementary
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let TL := (T : Subgroup G) ⊓ L
  have hE : E ≤ R := le_inf inf_le_left (inf_le_right.trans
    (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))
  have hEV : E ≤ centralizer (V : Set G) := inf_le_right.trans
    (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right))
  have hs : (T : Subgroup G) = TL ⊔ E := by
    rw [sylow_split_over_kernel h D structural A,
      kernel_pair_split h D structural A C hnone,← sup_assoc,
      sup_eq_left.mpr (le_inf D.le_sylow D.le_component)]
  have hn : ¬ U ≤ centralizer (V : Set G) := by
    intro hu
    have hz : U ⊓ V = ⊥ := C.transvections.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hu)
    have hc := C.hyperplane
    rw [hz,card_bot] at hc
    have hp : 1 < 2 ^ (d - 1) := one_lt_pow₀ (by decide) (by have := A.dimension.1; omega)
    omega
  obtain ⟨u,hu,huV⟩ := SetLike.not_le_iff_exists.mp hn
  have hprod : u ∈ (TL : Set G) * (E : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left TL E
      ((le_inf (inf_le_left.trans (T : Subgroup G).le_normalizer)
        (inf_le_left.trans D.sylow_normalizes_component)).trans inf_normalizer_le_normalizer_inf),← hs]
    exact C.core_le_sylow hu
  obtain ⟨l,hl,e,he,rfl⟩ := hprod
  have hlR : l ∈ R := by
    have hh := R.mul_mem (show l*e ∈ R from ⟨C.core_le_sylow hu,le_centralizer U hu⟩)
      (R.inv_mem (hE he))
    simpa only [mul_inv_cancel_right] using hh
  refine ⟨⟨l,hl.2⟩,hlR,?_⟩
  intro hlV
  exact huV ((centralizer (V : Set G)).mul_mem hlV (hEV he))

/-- The dimension-three kernel split uses a literal fixed involution to
exclude the exceptional natural cocycle. -/
theorem three_kernel_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  subst d
  let := D.elementary
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 R := radical_elementary h D structural A C hnone
  obtain ⟨l,hlR,hlV⟩ := exists_component_radical_noncentral h D structural A C hnone
  obtain ⟨e,f,hf⟩ := A.natural
  let a := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : a.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hl1 : a l ≠ 1 := by
    intro he
    have hcore : l ∈ pCore 2 L := hk ▸ (MonoidHom.mem_ker.mpr he)
    exact hlV (D.core_centralizes
      ((pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
        (mem_map_of_mem L.subtype hcore)))
  have hl2 : a l * a l = 1 := by
    rw [← map_mul]
    have he : l*l = 1 := Subtype.ext (by
      change (l : G)*(l : G) = 1
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (l : G) hlR)
    rw [he,map_one]
  have hVQ : V ≤ Q := le_inf D.le_sylow (le_centralizer V)
  have hZQ : Z ≤ Q := le_inf inf_le_left (inf_le_right.trans (centralizer_le D.le_component))
  apply le_antisymm _ (sup_le hVQ hZQ)
  intro q hq
  obtain ⟨v,hv,hvq⟩ := kernel_action_twist D A C
    (((structural G T L h).2.2 V D).1) hq
  let x := v*q
  have hxQ : x ∈ Q := Q.mul_mem (hVQ hv) hq
  have hxR : x ∈ R := ⟨hxQ.1,hvq⟩
  let N := V.subgroupOf L
  let eN : N ≃* Multiplicative (Fin 3 → ZMod 2) :=
    (subgroupOfEquivOfLe D.le_component).trans f
  let ρ := Representation.specialLinearNatural (k := ZMod 2) 3
  have heN (g : L) (w : Fin 3 → ZMod 2) :
      (eN.symm (Multiplicative.ofAdd (ρ (a g) w)) : L) =
        g * (eN.symm (Multiplicative.ofAdd w) : L) * g⁻¹ := by
    apply Subtype.ext
    change (f.symm (Multiplicative.ofAdd (ρ (a g) w)) : G) =
      (g : G) * (f.symm (Multiplicative.ofAdd w) : G) * (g : G)⁻¹
    simpa [a,ρ] using hf g (f.symm (Multiplicative.ofAdd w))
  let α : MulAut L := L.normalizerMonoidHom ⟨x,D.sylow_normalizes_component hxQ.1⟩
  have hdis (g : L) : α g * g⁻¹ ∈ N :=
    (kernel_commutator_eq D A C).le (commutator_mem_commutator hxQ g.property)
  have hfix (n : L) (hn : n ∈ a.ker) : α n = n := by
    apply Subtype.ext
    have hncore : n ∈ pCore 2 L := hk ▸ hn
    have hc := component_core_centralizes_kernel D A C (mem_map_of_mem L.subtype hncore) x hxQ
    change x*(n : G)*x⁻¹ = n
    change x * (n : G) = (n : G) * x at hc
    rw [hc,mul_inv_cancel_right]
  have hfixedl : α l = l := by
    apply Subtype.ext
    change x*(l : G)*x⁻¹ = l
    have hc : x * (l : G) = (l : G) * x := (le_centralizer R hxR l hlR).symm
    rw [hc,mul_inv_cancel_right]
  obtain ⟨n,hn⟩ := Representation.OneCohomology.automorphism_inner_of_fixed_element_of_subkernel
    N a ha eN ρ heN l (fun z hz =>
      Representation.OneCohomology.SLHigherNatural.SLThreeBinary.principal_of_zero_involution
        z (a l) hl1 hl2 hz) α hdis hfix hfixedl
  have hnV : ((n : L) : G) ∈ V := n.property
  have hnxZ : ((n : L) : G)*x ∈ Z := by
    refine ⟨(T : Subgroup G).mul_mem (D.le_sylow hnV) hxQ.1,?_⟩
    intro g hg
    have he := congrArg Subtype.val (hn ⟨g,hg⟩)
    change x*g*x⁻¹ = ((n : L) : G)⁻¹*g*((n : L) : G) at he
    calc
      g*(((n : L) : G)*x) = ((n : L) : G)*
        (((n : L) : G)⁻¹*g*((n : L) : G))*x := by group
      _ = ((n : L) : G)*(x*g*x⁻¹)*x := by rw [he]
      _ = (((n : L) : G)*x)*g := by group
  have hx : x ∈ V ⊔ Z := by
    have hh := (V ⊔ Z).mul_mem (mem_sup_left (V.inv_mem hnV)) (mem_sup_right hnxZ)
    simpa only [inv_mul_cancel_left] using hh
  have hh := (V ⊔ Z).mul_mem (mem_sup_left (V.inv_mem hv)) hx
  simpa only [x,inv_mul_cancel_left] using hh

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
