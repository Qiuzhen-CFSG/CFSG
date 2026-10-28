module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeWreath
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.WreathXi
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCentralizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete

/-!
# Xi in the original M22-code involution centralizer

The full wreath quotient constructs Xi membership for the literal embedded
O²(H), its actual elementary-nine two-core quotient, and H = O²(H)T.
The same original central involution then supplies the full Sylow restriction
inside C_G(z). All hypotheses of the adequate intrinsic embedding theorem
are constructed on this original subgroup and its Sylow three-complement.

The adequate conclusion retains its normal and Held alternatives. It does
not identify the detected component with the A₆-containing component, or
remove the possible central covering kernel of that A₆ marking. These
restrictions and the final dihedral/semidihedral contradiction remain
needed to remove the temporary inside-core assumption. The unconditional
M22-code exclusion and original-orbit M24-cocode selection remain separate
unfinished conclusions.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, using 1.3.1--4,
printed pp.508--511, refs/quasithin.pdf. The retained Held alternative
follows the correction in docs/quasithin-proof-basis.md.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.MathieuShadowRows Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original two-residual belongs to Xi, with its full elementary-nine
quotient and its original Sylow join. -/
theorem sourceOrbit_m22_code_inside_core_Xi
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    X ∈ Xi G (T : Subgroup G) ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
      X ⊔ (T : Subgroup G) = H := by
  obtain ⟨hp,hJ,⟨e⟩⟩ := D.sourceOrbit_m22_code_inside_core_wreath h hmany hV hnon d hH hcore
  let w := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  let S := T.subtype hH.1.1.2
  have htop : (⊤ : Subgroup H) ∈ Chapter1.H H := by
    intro hb
    apply hH.1.1.1
    have hm := congrArg (Subgroup.map H.subtype) hb
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective] at hm
    simpa only [←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hm
  have hXi := wreath_residual_mem_Xi S hp htop (e.trans w.symm)
  have hx := (mem_Xi_map_iff H.subtype H.subtype_injective).mpr hXi
  change (pResidual 2 H).map H.subtype ∈ Xi G
    (((T : Subgroup G).subgroupOf H).map H.subtype) at hx
  rw [map_subgroupOf_eq_of_le hH.1.1.2] at hx
  let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hj := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top S)
  have hSmap : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  rw [Subgroup.map_sup,hSmap,
    ←MonoidHom.range_eq_map,range_subtype] at hj
  exact ⟨hx,⟨aq.symm.trans (wreath_residual_core_equiv (e.trans w.symm))⟩,hj⟩

/-- The same involution centralizer admits the genuine Sylow-based Xi
embedding theorem. The Held alternative is retained explicitly. -/
theorem sourceOrbit_m22_code_inside_core_embedding
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P : Subgroup G,
        LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        AdequateConclusion 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) := by
  obtain ⟨hX,⟨e⟩,hjoin⟩ := D.sourceOrbit_m22_code_inside_core_Xi h hmany hV hnon d hH hcore
  obtain ⟨z,hne,ho,hTC,hHC,_⟩ :=
    D.sourceOrbit_m22_code_exists_centralizer_component h.toHypothesis1221 hnon d hH
  let X := (pResidual 2 H).map H.subtype
  let C := centralizer ({(z : G)} : Set G)
  let U := zpowers (z : G)
  have hUC : U ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCU : C ≤ normalizer (U : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer (U : Set G))
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro c hc
    exact mem_centralizer_singleton_iff.mp hc
  have hU2 : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le
    (zpowers_le.mpr z.property)
  have hUne : U ≠ ⊥ := by
    intro he
    exact hne (Subtype.ext (mem_bot.mp (he ▸ mem_zpowers (z : G))))
  have hCH : C ∈ Chapter1.H G := ne_bot_of_le_ne_bot hUne
    (le_pCoreIn_of_normalizes hU2 hUC hCU)
  have hS : IsSylowIn 2 (T : Subgroup G) C :=
    ⟨T.subtype hTC,map_subgroupOf_eq_of_le hTC⟩
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel) }
  have hodd : XiOddQuotient 3 (XiQuotient X) := Or.inl
    ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,by
      rw [Nat.card_congr e.toEquiv]; simp [Nat.card_eq_fintype_card]⟩
  let P : Sylow 3 X := Classical.arbitrary _
  have hin := localInput_of_mem_Xi hX hS (hjoin.le.trans hHC) (by decide : Odd 3) hodd P
  exact ⟨z,hne,ho,hHC,(P : Subgroup X).map X.subtype,hin,
    hin.adequate_knownSimple (Chapter3.sqtk_of_mem_H h.simpleQTKE hCH) hS⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
