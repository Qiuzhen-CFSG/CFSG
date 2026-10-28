module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PairGeometry
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Action

/-!
# The faithful original pair action in 12.6.26

For the original non-two pair I = <V,V^g>, conjugation on the actual
extraspecial seed P = <V5,V5^g> induces an action on P/Z(P). Its kernel
is I intersect O2(H), so the image I* in H/O2(H) is isomorphic to the
literal action image. The equivalence agrees with the original quotient
projection on each element of I.

The seed, its center, and the kernel are supplied by PairGeometry.
The first isomorphism theorem then constructs the compatible image
identification; no replacement group or assumed faithful action is used.
The plus-type and dihedral-order recognition remain separate obligations.
Source: Aschbacher--Smith, F.9.5(5--6.ii) and 12.6.26,
printed pp.319 and 831.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian
open Subgroup Theory.GroupTheory
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem centralAction_ker (I P Z : Subgroup G)
    (hn : I ≤ normalizer (P : Set G))
    (hz : (center P).map P.subtype = Z) (hIZ : I ≤ normalizer (Z : Set G)) :
    ((quotientAut (center P)).comp (seedConjugation I P hn)).ker =
      (commutatorPreimage I P Z).subgroupOf I := by
  ext x
  change quotientAut (center P) (seedConjugation I P hn x) = 1 ↔
    (x:G) ∈ commutatorPreimage I P Z
  rw [mem_commutatorPreimage_iff I P Z hIZ]
  simp only [x.property,true_and]
  constructor
  · intro hx p hp
    let pP : P := ⟨p,hp⟩
    have hh := DFunLike.congr_fun hx (QuotientGroup.mk' (center P) pP)
    rw [quotientAut_apply_mk] at hh
    have hc := QuotientGroup.eq_iff_div_mem.mp hh
    apply hz.le
    refine ⟨seedConjugation I P hn x pP / pP,hc,?_⟩
    change ((x:G)*p*(x:G)⁻¹)/p=⁅(x:G),p⁆
    simp only [div_eq_mul_inv,commutatorElement_def]
  · intro hx
    ext v
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hp := hx p p.property
    rw [←hz] at hp
    obtain ⟨z,hz',he⟩ := hp
    have he' : z = seedConjugation I P hn x p / p := by
      apply Subtype.ext
      change (z:G) = ((x:G)*(p:G)*(x:G)⁻¹)/(p:G)
      change (z:G) = ⁅(x:G),(p:G)⁆ at he
      simpa only [div_eq_mul_inv,commutatorElement_def] using he
    exact he' ▸ hz'

end CFSG.Quasithin.Chapter12.Section06.Nonabelian
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original pair image acts faithfully on its actual seed quotient,
compatibly with the quotient map H to H/O2(H). -/
theorem SourceHypothesis.original_non_two_pair_action
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let E := D.fullSetup hZ T z
    let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
    let P := E.pairSeed g
    ∃ (hIH : I ≤ H) (hnorm : I ≤ normalizer (P : Set G))
      (α : I →* MulAut (P ⧸ center P))
      (e : Nonabelian.Setup.star H I ≃* α.range),
      α = (quotientAut (center P)).comp (seedConjugation I P hnorm) ∧
      α.ker = (H.pCoreIn 2).subgroupOf I ∧
      ∀ i : I, (e ⟨QuotientGroup.mk' (pCore 2 H) (inclusion hIH i),
        mem_map_of_mem _ i.property⟩).val = α i := by
  let E := D.fullSetup hZ T z
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let P := E.pairSeed g
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  obtain ⟨hc,_,_,_,hk⟩ := S.original_non_two_pair_geometry D hZ z hz hTV hTz hbound hns hH g hg hn
  have hIH : I ≤ H := sup_le h.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact H.mul_mem (H.mul_mem hg (h.V_le_H hv)) (H.inv_mem hg))
  have hnorm : I ≤ normalizer (P : Set G) :=
    h.pair_normalizes_seed_join (E.perpendicular_index hz) g hg hn
  let α := (quotientAut (center P)).comp (seedConjugation I P hnorm)
  have hker : α.ker = (H.pCoreIn 2).subgroupOf I := by
    rw [Nonabelian.centralAction_ker I P E.V₁ hnorm hc
      (hIH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))),hk]
    ext x
    exact and_iff_right x.property
  let f := pairProjection (D := E.f9 H) I hIH
  have hk : f.ker = α.ker :=
    (pairProjection_ker (D := E.f9 H) I hIH).trans hker.symm
  let q := (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivRange α))
  let e : Nonabelian.Setup.star H I ≃* α.range :=
    (MulEquiv.subgroupCongr (pairProjection_range (D := E.f9 H) I hIH).symm).trans
      q
  refine ⟨hIH,hnorm,α,e,rfl,hker,?_⟩
  intro i
  change (q ⟨f i,⟨i,rfl⟩⟩).val = α i
  have hfi : (QuotientGroup.quotientKerEquivRange f).symm ⟨f i,⟨i,rfl⟩⟩ =
      QuotientGroup.mk' f.ker i :=
    (QuotientGroup.quotientKerEquivRange f).symm_apply_apply (QuotientGroup.mk' f.ker i)
  change ((QuotientGroup.quotientKerEquivRange α)
    ((QuotientGroup.quotientMulEquivOfEq hk)
      ((QuotientGroup.quotientKerEquivRange f).symm ⟨f i,⟨i,rfl⟩⟩))).val = α i
  rw [hfi]
  rfl

end CFSG.Quasithin.Chapter12.Section06
