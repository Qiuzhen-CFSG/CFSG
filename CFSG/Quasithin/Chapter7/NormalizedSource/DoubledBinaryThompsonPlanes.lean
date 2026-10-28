module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompson
public import Theory.Representation.BinaryPlaneNormalizer
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Theory.GroupTheory.TwoPerfectSmallAction
public import Stellmacher.ElementaryAbelianMaxGlobalClosure
public import Theory.Representation.NormalElementaryQuotient.OriginalAction

/-!
# The binary-plane step for the original Thompson quotient

A two-perfect normalizer of a nontrivial two-action on a binary plane fixes
its unique fixed line and hence the plane. For the symmetric-three Thompson
alternative, its moved plane has an invariant fixed complement. The original
two-residual's whole displacement is therefore Thompson-fixed. The residual
supplement to the original paired plane then forces J(H) to centralize the
full doubled orbit, contradicting the actual escaping-group generation.

The proof retains the original Sylow subgroup, its maximum-elementary
Thompson subgroup, and the literal quotient by the reduced module's
centralizer. The chosen-module application is in
NonFFSourceDoubledBinaryThompsonPlanes. Other Thompson alternatives remain
with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of Proposition 7.7.3, printed p.707,
refs/quasithin.pdf; the symmetric-three case is B.5.6(2), p.105.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonPlanes
open ChapterB.QuasisimpleSource

private theorem plane_fixed
    {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) G X) (R P : Subgroup G)
    (hR : IsPPerfect 2 R) (hP : IsPGroup 2 P)
    (hRP : R ≤ normalizer (P : Set G))
    (hd : Module.finrank (ZMod 2) X = 2)
    (hne : ∃ p : P, ρ p ≠ 1) : ∀ r : R, ρ r = 1 := by
  let C := fixedSpace ρ P
  have hCne : C ≠ ⊤ := by
    intro ht
    obtain ⟨p,hp⟩ := hne
    apply hp
    ext x
    exact (show x ∈ C from ht ▸ Submodule.mem_top) p
  have hdim : Module.finrank (ZMod 2) C ≤ 1 := by
    have hh := Submodule.finrank_lt hCne
    rw [hd] at hh
    omega
  have hstable : R ≤ subspaceStabilizer ρ C :=
    le_subspaceStabilizer ρ C (fun r hr x hx =>
      (fixedSpace_stable_of_normalizes ρ hRP hr x).2 hx)
  let τ : Representation (ZMod 2) R C :=
    Representation.subrepresentation (ρ.comp R.subtype) C
      (fun r x hx => (hstable r.property x).2 hx)
  let : MulAction R C := {
    smul r x := τ r x
    one_smul x := by change τ 1 x = x; rw [map_one]; rfl
    mul_smul r s x := by change τ (r*s) x = τ r (τ s x); rw [map_mul]; rfl }
  let : Finite C := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card C ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans_eq (by decide)
  have htopne : (⊤ : Submodule (ZMod 2) X) ≠ ⊥ := by
    intro he
    have hh : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) X) = 2 := by simpa using hd
    rw [he,finrank_bot] at hh
    omega
  obtain ⟨x,_,hx,hfix⟩ := PermutedSupports.exists_nonzero_fixed ρ P hP ⊤ htopne
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
  exact BinaryPlaneNormalizer.twoPerfect_plane_fixed (ρ.comp R.subtype) hR hd x hx
    (fun r => congrArg Subtype.val
      (MulAction.fixed_of_twoPerfect_of_card_le_two hR hcard r (⟨x,hfix⟩ : C)))

/-- The two-residual centralizes an invariant moved binary plane when it
normalizes a two-subgroup acting nontrivially on that plane. Its displacement
on the whole module is therefore fixed by the normal actor. -/
private theorem residual_moved_fixed
    {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) G X) (J R P : Subgroup G) [J.Normal]
    (hR : IsPPerfect 2 R) (hP : IsPGroup 2 P)
    (hRP : R ≤ normalizer (P : Set G))
    (hd : Module.finrank (ZMod 2) (moved ρ J) = 2)
    (hsplit : moved ρ J ⊔ fixedSpace ρ J = ⊤)
    (hne : ∃ p : P, ∃ x : moved ρ J, ρ p x ≠ x) :
    moved ρ R ≤ fixedSpace ρ J := by
  let U := (ChapterB.QuasisimpleSource.MovedSection.ofNormal ρ J).space
  have hn : ∃ p : P, U.toRepresentation p ≠ 1 := by
    obtain ⟨p,x,hx⟩ := hne
    refine ⟨p,?_⟩
    intro he
    exact hx (congrArg Subtype.val (LinearMap.congr_fun he x))
  have hfix := plane_fixed U.toRepresentation R P hR hP hRP hd hn
  apply Submodule.span_le.mpr
  rintro _ ⟨r,hr,x,_,rfl⟩
  obtain ⟨u,hu,c,hc,rfl⟩ := Submodule.mem_sup.mp (hsplit.ge (Submodule.mem_top (x := x)))
  have he : ρ r u = u := congrArg Subtype.val
    (LinearMap.congr_fun (hfix ⟨r,hr⟩) (⟨u,hu⟩ : U))
  have hc' : ρ r c ∈ fixedSpace ρ J :=
    (fixedSpace_stable_of_normal ρ J (mem_top r) c).2 hc
  rw [map_add,he,show u + ρ r c - (u+c) = ρ r c-c by abel]
  exact (fixedSpace ρ J).sub_mem hc' hc

/-- The split-plane argument needs normality only in its actual normalizer. -/
theorem relative_moved_fixed
    {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) G X) (A R P : Subgroup G)
    (hR : IsPPerfect 2 R) (hP : IsPGroup 2 P)
    (hRP : R ≤ normalizer (P : Set G))
    (hRA : R ≤ normalizer (A : Set G)) (hPA : P ≤ normalizer (A : Set G))
    (hd : Module.finrank (ZMod 2) (moved ρ A) = 2)
    (hsplit : moved ρ A ⊔ fixedSpace ρ A = ⊤)
    (hne : ∃ p : P, ∃ x : moved ρ A, ρ p x ≠ x) :
    moved ρ R ≤ fixedSpace ρ A := by
  let N := normalizer (A : Set G)
  let σ := ρ.comp N.subtype
  let A' := A.subgroupOf N
  let R' := R.subgroupOf N
  let P' := P.subgroupOf N
  have hR' : IsPPerfect 2 R' := hR.of_surjective
    (subgroupOfEquivOfLe hRA).symm.toMonoidHom (subgroupOfEquivOfLe hRA).symm.surjective
  have hP' : IsPGroup 2 P' := hP.of_equiv (subgroupOfEquivOfLe hPA).symm
  have hRP' : R' ≤ normalizer (P' : Set N) := by
    rw [← subgroupOf_normalizer_eq hPA]
    exact subgroupOf_mono N hRP
  have hm : moved σ A' = moved ρ A := by
    unfold moved
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le A.le_normalizer]
  have hf : fixedSpace σ A' = fixedSpace ρ A := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le A.le_normalizer]
  have hne' : ∃ p : P', ∃ x : moved σ A', σ p x ≠ x := by
    obtain ⟨p,x,hx⟩ := hne
    exact ⟨⟨⟨p,hPA p.property⟩,p.property⟩,⟨x,hm.symm ▸ x.property⟩,hx⟩
  have hh := residual_moved_fixed σ A' R' P' hR' hP' hRP'
    (hm ▸ hd) (by rwa [hm,hf]) hne'
  rw [hf] at hh
  have hmR : R'.map N.subtype = R := map_subgroupOf_eq_of_le hRA
  simpa only [moved,σ,subspaceCommutator_comp_map,hmR] using hh


/-- A normal split binary-plane actor in the original Thompson subgroup
modulo the action kernel centralizes the displacement of every two-perfect
normalizer of the Sylow Thompson subgroup. -/
theorem normal_plane_centralizes_residual
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (S : Sylow 2 H) (R A : Subgroup H)
    [A.Normal] (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer (Stellmacher.elementaryAbelianMaxJ (S : Subgroup H) : Set H))
    (hAJ : A ≤ Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H) ⊔ ρ.ker)
    (hd : Module.finrank (ZMod 2) (moved ρ A) = 2)
    (hsplit : moved ρ A ⊔ fixedSpace ρ A = ⊤) :
    moved ρ R ≤ fixedSpace ρ A := by
  let U := (ChapterB.QuasisimpleSource.MovedSection.ofNormal ρ A).space
  let P := Stellmacher.elementaryAbelianMaxJ (S : Subgroup H)
  have hP : IsPGroup 2 P := S.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
  have hmove : ∃ p : P, ∃ x : moved ρ A, ρ p x ≠ x := by
    by_contra! hn
    have hPK : P ≤ U.toRepresentation.ker := by
      intro p hp
      apply LinearMap.ext
      intro x
      exact Subtype.ext (hn ⟨p,hp⟩ x)
    have hJK : Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H) ≤
        U.toRepresentation.ker := by
      rw [Stellmacher.elementaryAbelianMaxJ_top_eq_normalClosure_sylow S]
      exact normalClosure_le_normal hPK
    have hker : ρ.ker ≤ U.toRepresentation.ker := by
      intro a ha
      apply LinearMap.ext
      intro x
      exact Subtype.ext (LinearMap.congr_fun ha x)
    have hAK := hAJ.trans (sup_le hJK hker)
    have htriv : ∀ a : A, ρ a = 1 := by
      intro a
      apply LinearMap.ext
      intro x
      obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp
        (hsplit.ge (Submodule.mem_top (x := x)))
      have he : ρ a u = u := congrArg Subtype.val
        (LinearMap.congr_fun (hAK a.property) (⟨u,hu⟩ : U))
      change ρ a (u + v) = u + v
      have hf : ρ a v = v := hv a
      rw [map_add,he,hf]
    have hz : moved ρ A = ⊥ := by
      apply bot_unique
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,x,_,rfl⟩
      change ρ a x - x = 0
      rw [htriv ⟨a,ha⟩,Module.End.one_apply,sub_self]
    rw [hz,finrank_bot] at hd
    omega
  exact residual_moved_fixed ρ A R P hR hP hRN hd hsplit hmove

open Stellmacher ChapterB.InternalThompsonAction DoubledBinaryThompson
open ChapterB.SourceInduction

/-- On the literal reduced action, the symmetric-three Thompson alternative
centralizes the commutator with every two-perfect normalizer of the original
Sylow Thompson subgroup. -/
private theorem symmetricThree_thompson_centralizes_commutator
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) [Y.Normal] [IsElementaryAbelian 2 Y]
    (S : Sylow 2 H) (R : Subgroup H) (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H))
    (c : SymmetricThreeCase (thompsonAction Y)) :
    elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ centralizer ((⁅Y,R⁆ : Subgroup H) : Set H) := by
  let J := elementaryAbelianMaxJ (⊤ : Subgroup H)
  let P := elementaryAbelianMaxJ (S : Subgroup H)
  let ρ := NormalElementaryQuotient.originalAction Y
  let : J.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hPJ : P ≤ J := elementaryAbelianMaxJ_sylow_le_top S
  have hP : IsPGroup 2 P := S.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
  have hρ : ρ = (action Y).comp (actionMk Y) := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.originalAction_apply Y a w).trans
      (action_apply Y a w).symm
  have hm : moved ρ J = moved (thompsonAction Y) ⊤ := by
    rw [hρ]
    unfold moved thompsonAction
    rw [subspaceCommutator_comp_map,subspaceCommutator_comp_map,
      ← MonoidHom.range_eq_map,range_subtype]
  have hf : fixedSpace ρ J = Representation.invariants (thompsonAction Y) := by
    rw [hρ]
    rw [fixedSpace_comp_map]
    rfl
  have hsplit : moved ρ J ⊔ fixedSpace ρ J = ⊤ := by
    rw [hm,hf]
    exact c.decomposition.sup_eq_top
  have hnc : ¬ P ≤ centralizer (Y : Set H) := by
    intro hc
    have hJC : J ≤ centralizer (Y : Set H) := by
      change elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ _
      rw [elementaryAbelianMaxJ_top_eq_normalClosure_sylow S]
      exact normalClosure_le_normal hc
    have hz : thompsonImage Y = ⊥ := by
      apply (map_eq_bot_iff J).mpr
      simpa only [actionMk,QuotientGroup.ker_mk'] using hJC
    have hn : Nontrivial (thompsonImage Y) := c.equiv.symm.injective.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hn hz
  have hmove : ∃ p : P, ∃ x : moved ρ J, ρ p x ≠ x := by
    by_contra! hn
    apply hnc
    intro p hp y hy
    let w : Additive Y := Additive.ofMul ⟨y,hy⟩
    obtain ⟨u,hu,v,hv,hw⟩ := Submodule.mem_sup.mp
      (hsplit.ge (Submodule.mem_top (x := w)))
    have he : ρ p w = w := by
      have hvf : ρ p v = v := hv ⟨p,hPJ hp⟩
      rw [← hw,map_add,hn ⟨p,hp⟩ ⟨u,hu⟩,hvf]
    have he' := congrArg (fun x : Additive Y => (x.toMul : H)) he
    rw [NormalElementaryQuotient.originalAction_apply] at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hh := residual_moved_fixed ρ J R P hR hP hRN (hm ▸ c.dimension) hsplit hmove
  intro j hj
  exact (NormalElementaryQuotient.original_moved_centralizer Y R j).mpr
    (fun w hw => hh hw ⟨j,hj⟩)

@[expose] def ReducedSymmetricThree
    {H : Type*} [Group H] (Y : Subgroup H) (hY : Theory.GroupTheory.IsPReduced 2 Y) : Prop :=
  let := hY.normal
  let := hY.elementary
  Nonempty (SymmetricThreeCase (thompsonAction Y))

/-- The symmetric-three alternative is incompatible with the original
escaping group, full orbit, residual supplement and Sylow Thompson normalizer. -/
theorem no_symmetricThree_escape
    {G : Type*} [Group G] [Finite G]
    (H Y W U R B M : Subgroup G) (S : Sylow 2 H)
    (hYH : Y ≤ H) (hWY : W ≤ Y) (hRH : R ≤ H)
    (hY : Theory.GroupTheory.IsPReduced 2 (Y.subgroupOf H))
    (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer
      (elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) : Set G))
    (hsupp : U ⊔ ⁅W,R⁆ = W) (hHC : H ≤ centralizer (U : Set G))
    (hWM : centralizer (W : Set G) ≤ M) (hBM : B ≤ M)
    (hgen : H = elementaryAbelianMaxJ H ⊔ B) (hout : ¬ H ≤ M) :
    ¬ ReducedSymmetricThree (Y.subgroupOf H) hY := by
  let := hY.normal
  let := hY.elementary
  rintro ⟨c⟩
  have hR' : IsPPerfect 2 (R.subgroupOf H) := hR.of_surjective
    (subgroupOfEquivOfLe hRH).symm.toMonoidHom (subgroupOfEquivOfLe hRH).symm.surjective
  have heP : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) :=
    (elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective _).symm
  have hRN' : R.subgroupOf H ≤
      normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) := by
    have hh := subgroupOf_mono H hRN
    rw [← heP,subgroupOf_normalizer_eq (map_subtype_le _)] at hh
    simpa only [subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hc := symmetricThree_thompson_centralizes_commutator
    (Y.subgroupOf H) S (R.subgroupOf H) hR' hRN' c
  have hh := congrArg (Subgroup.map H.subtype)
    (commutator_eq_bot_iff_le_centralizer.mpr hc)
  have heJ : (elementaryAbelianMaxJ (⊤ : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ H := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      ← MonoidHom.range_eq_map,range_subtype]
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hYH,
    map_subgroupOf_eq_of_le hRH,heJ,Subgroup.map_bot] at hh
  have hJW : elementaryAbelianMaxJ H ≤ centralizer (W : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hsupp]
    apply sup_le
    · exact le_centralizer_iff.mp ((show elementaryAbelianMaxJ H ≤ H from
        sSup_le fun _ hA => hA.1).trans hHC)
    · exact (commutator_mono hWY le_rfl).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
  apply hout
  rw [hgen]
  exact sup_le (hJW.trans hWM) hBM

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonPlanes
