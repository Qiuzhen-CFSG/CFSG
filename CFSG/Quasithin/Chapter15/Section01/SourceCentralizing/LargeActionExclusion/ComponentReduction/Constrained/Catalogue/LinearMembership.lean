module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalApplications
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalNormality
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.NormalizedPerfect
public import Theory.GroupTheory.EquivariantParabolicLift
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedAutomorphism
public import Theory.Representation.SL3RepeatedNaturalFlagTypes
public import Theory.SpecificGroups.PSL3.SplitPrimeRank

/-!
# Linear-three residuals in the original local family

A prime dividing q−1 has rank two in SL₃(q). The original strongly
quasithin and cubic-center bounds therefore force S to normalize K.
Align its Sylow intersection once with the standard unitriangular group.
The actual B.5 moved section, or moved space in the doubled-natural row,
is preserved by the original quotient action. Its natural-module
intertwiner distinguishes the two flag types, so both parabolics and
their solvable residuals are S-normalized.

The residuals are the literal preimages in K N_S(K), identified with their
pullbacks in K. Their proved SL₂ core quotients, perfectness and nontrivial
two-cores establish membership in L(G₁,S). No ambient componenthood,
S-normalization, Borel equality or parabolic-marking premise is added.
`HigherLinear` applies the original nonblock theorem to these memberships.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095, using
A.3.8(3) and the natural and doubled-natural rows of B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Every higher-field SL₃ core quotient forces normalization by the original S. -/
theorem localFamily_linear_three_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) : d.S ≤ normalizer (K : Set G) := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have hEven : Even (Nat.card F) := by rw [hF]; exact Nat.even_pow.mpr ⟨by decide,by omega⟩
    have ho : Odd (Nat.card F - 1) := Nat.Even.sub_odd (by omega) hEven (by decide)
    exact ho.not_two_dvd_nat hd
  have ho : Odd p := hp.odd_of_ne_two hp2
  let : Fact p.Prime := ⟨hp⟩
  apply d.localFamily_normalizes_of_oddRank hG h hK hq hp ho
  rw [primeRank_equiv p e]
  exact Matrix.PSL3.SplitPrimeRank.special_rank F hd

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

private theorem moved_linear_three_flags
    (ρ : Representation (ZMod 2) D W) (L J : Subgroup D) [L.Normal]
    (hLJ : L ≤ J) (s : MovedSection (ρ.comp J.subtype) (L.subgroupOf J))
    (F : BinaryField) {r : ℕ} (hr : 0 < r)
    (hm : Nonempty (ActionEquiv (s.action.comp (L.subgroupOf J).subtype)
        (repeated (linearNatural F 3) r)) ∨
      Nonempty (ActionEquiv (s.space.toRepresentation.comp (L.subgroupOf J).subtype)
        (repeated (linearNatural F 3) r)))
    (e : L ≃* SL(3,F.Carrier)) (t : D)
    (hU : (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).map
      (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom =
        Matrix.PSL3.LinearThree.unipotentSL F.Carrier) :
    (Matrix.PSL3.LinearThree.pointParabolicSL F.Carrier).map
        (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom =
      Matrix.PSL3.LinearThree.pointParabolicSL F.Carrier ∧
    (Matrix.PSL3.LinearThree.lineParabolicSL F.Carrier).map
        (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom =
      Matrix.PSL3.LinearThree.lineParabolicSL F.Carrier := by
  let i : L.subgroupOf J ≃* L := subgroupOfEquivOfLe hLJ
  let β : MulAut (L.subgroupOf J) := i.trans ((MulAut.conjNormal t).trans i.symm)
  let b := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  have hb (l : L.subgroupOf J) (w : W) :
      b ((ρ.comp J.subtype) l w) = (ρ.comp J.subtype) (β l) (b w) := by
    change ρ t (ρ l.val.val w) = ρ (t*l.val.val*t⁻¹) (ρ t w)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  rcases hm with hc | hc
  · obtain ⟨c⟩ := hc
    let E := s.twistedActionEquiv β b hb
    let B := c.linearEquiv.symm.trans (E.linearEquiv.trans c.linearEquiv)
    let f := e.symm.trans (i.symm.trans c.groupEquiv)
    apply SL3RepeatedNaturalFlagTypes.flags_of_intertwiner _ hU f hr B
    intro g w
    have hi := c.conjugate_intertwiner β E.linearEquiv
      (s.twistedActionEquiv_intertwines β b hb) (f g) w
    change B (fun j => (f g).val.mulVec (w j)) =
      (fun j => ((c.groupEquiv.symm.trans (β.trans c.groupEquiv)) (f g)).val.mulVec ((B w) j)) at hi
    simpa only [f,β,i,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,
      MulEquiv.apply_symm_apply] using hi
  · obtain ⟨c⟩ := hc
    let E := s.twistedSpaceEquiv β b hb
    let B := c.linearEquiv.symm.trans (E.trans c.linearEquiv)
    let f := e.symm.trans (i.symm.trans c.groupEquiv)
    apply SL3RepeatedNaturalFlagTypes.flags_of_intertwiner _ hU f hr B
    intro g w
    have hi := c.conjugate_intertwiner β E
      (s.twistedSpaceEquiv_intertwines β b hb) (f g) w
    change B (fun j => (f g).val.mulVec (w j)) =
      (fun j => ((c.groupEquiv.symm.trans (β.trans c.groupEquiv)) (f g)).val.mulVec ((B w) j)) at hi
    simpa only [f,β,i,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,
      MulEquiv.apply_symm_apply] using hi
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The binary representation of the literal normalizer centralizer quotient. -/
noncomputable abbrev NormalizerAction.representation
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K) :=
  letI := a.reduced.elementary
  NormalElementaryQuotient.representation (d.normalizerModule K)
    (QuotientGroup.mk' (centralizer (d.normalizerModule K :
      Set (K ⊔ d.normalizerSylow K : Subgroup G))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- The actual repeated natural section supplies both literal residual memberships
after one Sylow conjugation. It permits the original natural and doubled rows. -/
theorem localFamily_linear_residual_members
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (a : d.NormalizerAction K) :
    letI := a.reduced.elementary
    ∀ (J : Subgroup ((K ⊔ d.normalizerSylow K : Subgroup G) ⧸
        centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G))))
      (_hLJ : d.normalizerImage K ≤ J)
      (s : MovedSection (a.representation.comp J.subtype) ((d.normalizerImage K).subgroupOf J))
      (F : BinaryField) (r : ℕ), 0 < r → 1 < F.degree →
      (Nonempty (ActionEquiv (s.action.comp ((d.normalizerImage K).subgroupOf J).subtype)
          (repeated (linearNatural F 3) r)) ∨
       Nonempty (ActionEquiv (s.space.toRepresentation.comp ((d.normalizerImage K).subgroupOf J).subtype)
          (repeated (linearNatural F 3) r))) →
    ∃ e' : d.normalizerImage K ≃* SL(3,F.Carrier),
      ∀ P ∈ ({pointParabolicSL F.Carrier,lineParabolicSL F.Carrier} : Set (Subgroup SL(3,F.Carrier))),
        d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom) ∈ Chapter1.LIn d.G1 d.S := by
  let := a.reduced.elementary
  intro J hLJ s F r hr hn hm
  have he : Nonempty (d.normalizerImage K ≃* SL(3,F.Carrier)) := by
    rcases hm with hc | hc
    · obtain ⟨c⟩ := hc
      exact ⟨(subgroupOfEquivOfLe hLJ).symm.trans c.groupEquiv⟩
    · obtain ⟨c⟩ := hc
      exact ⟨(subgroupOfEquivOfLe hLJ).symm.trans c.groupEquiv⟩
  obtain ⟨e⟩ := he
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let ec := (MulEquiv.ofBijective a.coreToImage
    (a.linear_three_core_bijective hG h hK.1 hq hfour e)).trans e
  have hnK := d.localFamily_linear_three_normalizes hG h hK hq F.card_eq hn ec
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q₀ := e.toMonoidHom.comp (d.toNormalizerImage K)
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (d.toNormalizerImage_surjective K)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(3,F.Carrier)) (Q.mapSurjective hq₀)
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F.Carrier F.degree_pos F.card_eq)
  let e' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (d.toNormalizerImage K)
  have hU : (Q : Subgroup K).map q = unipotentSL F.Carrier := by
    have hh := congrArg (fun U : Sylow 2 SL(3,F.Carrier) => (U : Subgroup SL(3,F.Carrier))) hg
    change ((Q : Subgroup K).map q₀).map (MulAut.conj g).toMonoidHom = unipotentSL F.Carrier at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.S ⊓ K ≤ K from inf_le_right)]
    exact hQ
  let H := K ⊔ d.normalizerSylow K
  let qH := QuotientGroup.mk' (centralizer (d.normalizerModule K : Set H))
  let : (d.normalizerImage K).Normal := by
    change ((K.subgroupOf H).map qH).Normal
    rw [a.fitting]
    infer_instance
  have hSH : d.S ≤ H := by
    have he : d.normalizerSylow K = d.S := inf_eq_left.mpr hnK
    change d.S ≤ K ⊔ d.normalizerSylow K
    rw [he]
    exact le_sup_right
  let j : d.S →* H := inclusion hSH
  let α : d.S →* MulAut SL(3,F.Carrier) := (MulAut.congr e').toMonoidHom.comp
    (MulAut.conjNormal.comp (qH.comp j))
  have heq (x : d.S) (k : K) :
      q (K.normalizerMonoidHom (inclusion hnK x) k) = α x (q k) := by
    change e' (d.toNormalizerImage K _) =
      e' ((MulAut.conjNormal (qH (j x))) (e'.symm (e' (d.toNormalizerImage K k))))
    rw [e'.symm_apply_apply]
    congr 1
  have hnSK : d.S ≤ normalizer ((d.S ⊓ K) : Set G) :=
    (le_inf d.S.le_normalizer hnK).trans inf_normalizer_le_normalizer_inf
  have hUi (x : d.S) : (unipotentSL F.Carrier).map (α x).toMonoidHom = unipotentSL F.Carrier := by
    have hh := EquivariantLift.map_invariant K q hnK α heq (D := d.S ⊓ K) hnSK x
    rw [←hQL,hU] at hh
    exact hh
  have hpair (x : d.S) :
      (pointParabolicSL F.Carrier).map (α x).toMonoidHom = pointParabolicSL F.Carrier ∧
      (lineParabolicSL F.Carrier).map (α x).toMonoidHom = lineParabolicSL F.Carrier :=
    moved_linear_three_flags a.representation (d.normalizerImage K) J hLJ s F hr hm
      e' (qH (j x)) (hUi x)
  refine ⟨e',?_⟩
  intro P hP
  have hPi (s : d.S) : P.map (α s).toMonoidHom = P := by
    rcases hP with rfl | hP
    · exact (hpair s).1
    · have he : P = lineParabolicSL F.Carrier := hP
      subst P
      exact (hpair s).2
  let B := (P.comap q).map K.subtype
  let R := d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom)
  have hR : R = (solvableResidual B).map B.subtype := by
    dsimp only [R]
    rw [d.normalizerParabolicResidual_eq_in_K]
    have he : (P.map e'.symm.toMonoidHom).comap (d.toNormalizerImage K) = P.comap q := by
      ext k
      change d.toNormalizerImage K k ∈ P.map e'.symm.toMonoidHom ↔ e' (d.toNormalizerImage K k) ∈ P
      constructor
      · rintro ⟨y,hy,he⟩
        rw [←he]
        change e' (e'.symm y) ∈ P
        rw [e'.apply_symm_apply]
        exact hy
      · intro hx
        exact ⟨_,hx,e'.symm_apply_apply _⟩
    rw [he,map_embedded_solvableResidual_of_hom]
  have hnB : d.S ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx b hb
    obtain ⟨k,hk,rfl⟩ := hb
    let x₀ : d.S := ⟨x,hx⟩
    refine ⟨K.normalizerMonoidHom (inclusion hnK x₀) k,?_,rfl⟩
    change q (K.normalizerMonoidHom (inclusion hnK x₀) k) ∈ P
    rw [heq]
    exact hPi x₀ ▸ mem_map_of_mem (α x₀).toMonoidHom hk
  have hnR : d.S ≤ normalizer (R : Set G) := by
    rw [hR]
    exact hnB.trans (normalizer_le_normalizer_characteristic_image B (solvableResidual B))
  let : Group.IsPerfect R := hR ▸ Group.IsPerfect.map B.subtype
  obtain ⟨hfit,⟨er⟩⟩ := a.linear_three_residual_data hG h hK.1 hq hfour e' P hP
  let : IsSimpleGroup SL(2,F.Carrier) := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple (by omega)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := er.isSimpleGroup
  let : Nontrivial R := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (pCore 2 R))
  have hz : center (R ⧸ pCore 2 R) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (R ⧸ pCore 2 R)) inferInstance with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : R.pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hb : pCore 2 R = ⊥ := (map_eq_bot_iff_of_injective _ R.subtype_injective).mp hh
    have ht := centralizer_generalizedFitting_le R
    rw [hfit,hb] at ht
    rw [show centralizer ((⊥ : Subgroup R) : Set R) = ⊤ from
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup R) ≤ center R from bot_le)] at ht
    have ht' : (⊤ : Subgroup R) = ⊥ := bot_unique ht
    exact (top_ne_bot : (⊤ : Subgroup R) ≠ ⊥) ht'
  exact ⟨(d.normalizerParabolicResidual_le K _).trans hK.1,
    (Chapter1.mem_LIn_of_normalized_perfect hK.2.2.1
      ((d.normalizerParabolicResidual_le K _).trans le_sup_left) hnR hc).2⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
