module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Scalar
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Arithmetic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Tori
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple

/-!
# Excluding both marked symplectic embeddings over every binary field

The literal central quotient marking lifts to the whole perfect component
because the nonbinary symplectic multiplier is trivial. Its local subgroup
then has the actual SL₂ core quotient. Choose a prime dividing the scalar
torus and avoiding the field degree. The scalar moves every nonzero radical
subgroup, whereas the original pair's prime residual forces it to fix [V,L].

No equality of [V,L] with the radical or irreducibility of a fixed setup
is needed. The embedding inspection must still construct one of the two
literal parabolic markings; a bare group-family tag does not supply it.
Source: Aschbacher--Smith 10.2.9, printed pp.750--751, using I.1.3.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02 Chapter4 Theory.SpecificGroups.SymplecticFour
universe u

private theorem scalar_image {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) (P : Subgroup H)
    (L W : Subgroup G) (hP : P.map f = L)
    (hW : W ≤ L.pCoreIn 2) (hne : W ≠ ⊥)
    {x : H} (p : ℕ) (hx : orderOf x = p) (hn : x ∈ normalizer (P : Set H))
    (hc : ∀ b ∈ P, ⁅x,b⁆ ∈ P.pCoreIn 2)
    (hfix : ∀ q ∈ P.pCoreIn 2, Commute q x → q = 1) :
    orderOf (f x) = p ∧ f x ∈ sectionCentralizer L ∧
      f x ∉ centralizer (W : Set G) := by
  have hcore : (P.pCoreIn 2).map f = L.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 P f hf, hP]
  refine ⟨(orderOf_injective f hf x).trans hx, ?_, ?_⟩
  · apply (mem_commutatorPreimage_iff (normalizer (L : Set G)) L (L.pCoreIn 2)
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L)) (f x)).mpr
    constructor
    · rw [←hP]
      exact P.le_normalizer_map f (mem_map_of_mem f hn)
    · intro b hb
      obtain ⟨a,ha,rfl⟩ := hP.symm ▸ hb
      rw [←hcore, ←map_commutatorElement]
      exact mem_map_of_mem f (hc a ha)
  · intro hcentral
    obtain ⟨w,hwn⟩ := ne_bot_iff_exists_ne_one.mp hne
    have hw : (w : G) ∈ (P.pCoreIn 2).map f := hcore.symm ▸ hW w.property
    obtain ⟨q,hq,hqw⟩ := hw
    have hcomm : Commute q x := by
      apply hf
      simpa only [map_mul,hqw] using (mem_centralizer_iff.mp hcentral w w.property)
    have hw1 : (w : G) = 1 := hqw.symm.trans (by rw [hfix q hq hcomm,map_one])
    exact hwn (Subtype.ext hw1)


variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem symplectic_local_impossible
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (P : Subgroup (Sp F)) (f : Sp F →* G) (hf : Function.Injective f)
    (hP : P.map f = L)
    (eP : (P ⧸ pCore 2 P) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hscalar : ∀ (p : ℕ) [Fact p.Prime], p ∣ 2 ^ n - 1 →
      ∃ x : Sp F, orderOf x = p ∧ x ∈ normalizer (P : Set (Sp F)) ∧
        (∀ b ∈ P, ⁅x,b⁆ ∈ P.pCoreIn 2) ∧
        ∀ q ∈ P.pCoreIn 2, Commute q x → q = 1) : False := by
  let a : P ≃* L := (P.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hP)
  let e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.congr _ _ a.symm (pCore_map_iso 2 a.symm)).trans eP
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) at hh
    rw [Theory.PSL2.sl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  obtain ⟨p,hp,hp2,hpd,hpn⟩ := exists_scalar_prime hn
  let : Fact p.Prime := ⟨hp⟩
  have hd : p ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    have hdiv : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      have he : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        nlinarith [Nat.sub_add_cancel hpow, Nat.sub_add_cancel (Nat.one_le_pow 2 (2 ^ n) (by positivity))]
      rw [he]
      exact dvd_mul_right _ _
    exact (hpd.trans hdiv).trans (dvd_mul_left _ _)
  have ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))) := by
    rw [Nat.card_congr (MulAut.outerCongr (e.trans (Theory.PSL2.sl2QuotientEquiv F))).toEquiv,
      Theory.PSL2.outer_card_eq_field_degree F hF]
    exact hpn
  obtain ⟨x,hx,hnx,hcx,hfix⟩ := hscalar p hpd
  obtain ⟨hx',hc',hm'⟩ := scalar_image f hf P L ⁅D.fullModule,L⁆ hP
    (source_full_moved_le_component_core D) (source_full_moved_ne_bot D)
    p hx hnx hcx hfix
  exact moving_prime_scalar_impossible D hz p hp2 hd ho c hx' hc' hm'

/-- The full nonbinary symplectic exception is impossible for the literal
point or plane marking of L inside the central quotient of I. -/
theorem symplectic_marking_impossible
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [Group.IsPerfect I] (c : EscapingComponent D t v I)
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (eI : (I ⧸ center I) ≃* Sp F)
    (hmark : (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = pointLocal ∨
      (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = planeLocal) : False := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  obtain ⟨eWhole,heWhole⟩ := CentralCovers.Even.exists_whole_model hF hn eI
  have heMap : eWhole.toMonoidHom = eI.toMonoidHom.comp (QuotientGroup.mk' (center I)) := by
    ext i : 1
    exact heWhole i
  let f := I.subtype.comp eWhole.symm.toMonoidHom
  have hf : Function.Injective f := I.subtype_injective.comp eWhole.symm.injective
  have hmark' : (L.subgroupOf I).map eWhole.toMonoidHom = pointLocal ∨
      (L.subgroupOf I).map eWhole.toMonoidHom = planeLocal := by
    rwa [heMap]
  have hmap (P : Subgroup (Sp F)) (hp : (L.subgroupOf I).map eWhole.toMonoidHom = P) :
      P.map f = L := by
    rw [←hp,Subgroup.map_map]
    have he : f.comp eWhole.toMonoidHom = I.subtype := by
      ext i
      simp [f]
    rw [he,map_subgroupOf_eq_of_le c.strict.le]
  rcases hmark' with hp | hp
  · exact symplectic_local_impossible D c hF hn pointLocal f hf (hmap _ hp)
      (pointLocalCoreQuotientEquiv hF hn) (fun p _ hp => point_prime_scalar hF hn hp)
  · exact symplectic_local_impossible D c hF hn planeLocal f hf (hmap _ hp)
      (planeLocalCoreQuotientEquiv hF hn) (fun p _ hp => plane_prime_scalar hF hn hp)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
