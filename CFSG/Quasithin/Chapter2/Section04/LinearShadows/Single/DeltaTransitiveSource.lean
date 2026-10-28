module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import Theory.GroupTheory.PairFactorAction
/-!
# The two-coordinate orbit in the original Sylow center

In the nontrivial-center branch, Z(R)=Z×Zˣ. The original torus D fixes Z
and its conjugate acts regularly on Z. Conjugating reverses the roles of
the two factors. Their product B is therefore transitive on the elements
with both coordinates nonidentity, the source set Δ.

Source: Aschbacher–Smith, 2.4.20(1), printed p.535.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

@[expose] def distinguishedDelta (d : MinimalBlockSetup M) (x : G) : Set G :=
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  {u | u ∈ R ⊓ centralizer (R : Set G) ∧ u ∉ distinguishedZ d ∧
    u ∉ (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom}

theorem source_distinguished_delta_transitive
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxB : x ∈ normalizer (c.hall : Set G)) :
    ∀ u ∈ distinguishedDelta d x, ∀ v ∈ distinguishedDelta d x,
      ∃ b ∈ c.hall, b*u*b⁻¹=v := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L := d.block.map d.H.subtype
  let Z := distinguishedZ d
  let W := Z.map (MulAut.conj x⁻¹).toMonoidHom
  let E := c.torus.map (MulAut.conj x⁻¹).toMonoidHom
  have hp := source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS
  have ht := d.lemma_2_4_8_1 hG T hST hsingle
    (hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective))
  have hzS := (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.2.2
  have hx2 : x^2 ∈ S := (S.subgroupOf (T : Subgroup G)).sq_mem_of_index_two ht.1 (⟨x,hxT⟩ : T)
  have hz2 : Z.map (MulAut.conj (x^2)).toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp (hzS hx2)
  have hxZ : Z.map (MulAut.conj x).toMonoidHom = W := by
    apply map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
    have hh : (Z.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = Z :=
      (conjBy_mul Z x x).symm.trans (by simpa only [pow_two,Subgroup.conjBy] using hz2)
    exact hh.trans (conjBy_inv' Z x).symm
  have hDo : Odd (Nat.card c.torus) := c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall)
  have hEL := (source_conjugate_torus_normalizes_block d hG T hST hsingle hL hM hTM hunique
    c.torus hDo (c.torus_le_hall.trans c.hall_normalizes) x hxT hxS).2.2
  have hr := (source_center_torus_of_choice d hG T hST hsingle hL hM hTM hunique
    c.torus c.hall x hxT (c.torus_le.trans inf_le_right) hDo c.torus_card
    (c.conjugate_pair x hxT hxS hxB) c.hall_fixed hEL).resolve_left hz
  have hEZ : ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ a ∈ E, a*z*a⁻¹=w := by
    intro z hzZ hz1 w hwZ hw1
    have hzZ' : z ∈ (center L).map L.subtype := (distinguishedZ_of_center_ne_bot d hz).le hzZ
    have hwZ' : w ∈ (center L).map L.subtype := (distinguishedZ_of_center_ne_bot d hz).le hwZ
    obtain ⟨a,ha,_⟩ := hr.2.2 ⟨z,hzZ'⟩ (fun he => hz1 (congrArg Subtype.val he))
      ⟨w,hwZ'⟩ (fun he => hw1 (congrArg Subtype.val he))
    exact ⟨a,a.property,ha⟩
  have hDW : ∀ z ∈ W, z ≠ 1 → ∀ w ∈ W, w ≠ 1 → ∃ a ∈ c.torus, a*z*a⁻¹=w := by
    have hh := conjugate_factor_transitive E Z (MulAut.conj x) hEZ
    have he : E.map (MulAut.conj x).toMonoidHom = c.torus := conjBy_inv' c.torus x
    rwa [he,hxZ] at hh
  have hDZ : c.torus ≤ centralizer (Z : Set G) := by
    intro a ha
    apply mem_centralizer_iff.mpr
    intro z hzZ
    obtain ⟨z,hz,rfl⟩ := (distinguishedZ_of_center_ne_bot d hz).le hzZ
    exact (congrArg Subtype.val (mem_center_iff.mp hz (⟨a,(c.torus_le.trans inf_le_right) ha⟩ : L))).symm
  have hEW : E ≤ centralizer (W : Set G) := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨z,hzZ,rfl⟩
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj x⁻¹) ((mem_centralizer_iff.mp (hDZ ha)) z hzZ)
  have hEB : E ≤ c.hall := (map_mono c.torus_le_hall).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer (c.hall : Set G)).inv_mem hxB))
  have hWZ : W ≤ centralizer (Z : Set G) :=
    ((le_sup_right.trans hp.2.le).trans inf_le_right).trans
      (centralizer_le ((le_sup_left.trans hp.2.le).trans inf_le_left))
  intro u hu v hv
  exact transitive_on_sup_complement_of_factor_actions Z W E c.torus c.hall hWZ hEB c.torus_le_hall
    hEW hDZ hEZ hDW u v (hp.2.ge hu.1) hu.2.1 hu.2.2 (hp.2.ge hv.1) hv.2.1 hv.2.2
end CFSG.Quasithin.Chapter2.LinearShadows.Single
