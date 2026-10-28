module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaCentralSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FixedSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.OrthogonalSingularGeometry
/-!
# The original outside center is the singular line

The original torus is transitive on the nonidentity elements of the outside
center factor. That factor centralizes the original Sylow subgroup of the
block, so its quadratic form is additive in the marked orthogonal coordinates.
The regular orbit forces the form to vanish. Transitivity on nonzero singular
vectors then gives fusion with any prescribed nonidentity distinguished-center
element, through the original block and ambient conjugation maps.

Source: Aschbacher–Smith, 2.4.16 and the orthogonal argument in 2.4.21, p.536.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_distinguished_torus_transitive_on_outside_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxB : x ∈ normalizer (c.hall : Set G)) :
    ∀ z ∈ (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom, z ≠ 1 →
      ∀ w ∈ (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom, w ≠ 1 →
      ∃ b ∈ c.torus, b*z*b⁻¹=w := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L := d.block.map d.H.subtype
  let Z := distinguishedZ d
  let W := Z.map (MulAut.conj x⁻¹).toMonoidHom
  let E := c.torus.map (MulAut.conj x⁻¹).toMonoidHom
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
  exact hDW

theorem source_outside_center_singular_of_normalizes_hall
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxB : x ∈ normalizer (c.hall : Set G))
    {b : MulAut (d.block.map d.H.subtype)}
    (e : ChapterC.OrthogonalInvolutionCoordinates (d.block.map d.H.subtype) n b)
    (u : pCore 2 (d.block.map d.H.subtype))
    (hu : ((u : d.block.map d.H.subtype) : G) ∈
      (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom) :
    Representation.SL2OrthogonalCover.form (e.core u).toAdd=0 := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  let W := (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom
  have hWZ : W ≤ R ⊓ centralizer (R : Set G) := le_sup_right.trans
    (source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS).2.le
  have hWU : W ≤ U := hWZ.trans ((source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left)
  have hcore : (pCore 2 L).map L.subtype=U := by
    rw [source_block_core_eq_module d hG T hST hsingle]
    rfl
  have hWcore : W.subgroupOf L ≤ pCore 2 L := by
    intro w hw
    obtain ⟨v,hv,he⟩ := hcore.ge (hWU hw)
    exact (Subtype.ext he : v=w) ▸ hv
  obtain ⟨P,hP⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.1
  have hWP : ∀ w ∈ W.subgroupOf L, ∀ p ∈ (P : Subgroup L), Commute w p := by
    intro w hw p hp
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hWZ hw).2 p.val (hP.le (mem_map_of_mem L.subtype hp))).symm
  have hWL : W ≤ L := hWU.trans (map_subtype_le _)
  have hcard : 2<Nat.card (W.subgroupOf L) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv,
      Nat.card_congr (equivMapOfInjective (distinguishedZ d) (MulAut.conj x⁻¹).toMonoidHom
        (MulAut.conj x⁻¹).injective).toEquiv.symm,
      (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.1]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hL.1)
  have htrans : ∀ v : W.subgroupOf L, v≠1 → ∀ w : W.subgroupOf L, w≠1 →
      ∃ l : L, l*v.val*l⁻¹=w.val := by
    intro v hv w hw
    obtain ⟨l,hl,he⟩ := source_distinguished_torus_transitive_on_outside_center
      d hG T hST hsingle hL hM hTM hunique c hz x hxT hxS hxB
      v.val.val v.property (fun hh => hv (Subtype.ext (Subtype.ext hh)))
      w.val.val w.property (fun hh => hw (Subtype.ext (Subtype.ext hh)))
    exact ⟨⟨l,(c.torus_le.trans inf_le_right) hl⟩,Subtype.ext he⟩
  exact e.singular_of_regular_sylow_fixed P (W.subgroupOf L) hWcore hWP hcard htrans u.val hu


theorem source_outside_center_singular
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    {b : MulAut (d.block.map d.H.subtype)}
    (e : ChapterC.OrthogonalInvolutionCoordinates (d.block.map d.H.subtype) n b)
    (u : pCore 2 (d.block.map d.H.subtype))
    (hu : ((u : d.block.map d.H.subtype) : G) ∈
      (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom) :
    Representation.SL2OrthogonalCover.form (e.core u).toAdd=0 := by
  obtain ⟨y,hyT,hyS,hyB⟩ := c.outside
  apply source_outside_center_singular_of_normalizes_hall d hG T hST hsingle hL hM hTM hunique
    c hz y hyT hyS hyB e u
  exact (source_distinguished_outside_conjugate_eq d hG T hST hsingle hL hM hTM hunique
    x y hxT hxS hyT hyS).le hu



theorem source_singular_fused_distinguished
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    {b : MulAut (d.block.map d.H.subtype)}
    (e : ChapterC.OrthogonalInvolutionCoordinates (d.block.map d.H.subtype) n b)
    (u : pCore 2 (d.block.map d.H.subtype))
    (hu : Representation.SL2OrthogonalCover.form (e.core u).toAdd=0) (hu1 : u≠1)
    (z : G) (hzZ : z∈distinguishedZ d) (hz1 : z≠1) :
    IsConj z ((u : d.block.map d.H.subtype) : G) := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  obtain ⟨x,hxT,hxS,hxB⟩ := c.outside
  let w := (MulAut.conj x⁻¹) z
  have hwZ : w∈(distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom := mem_map_of_mem _ hzZ
  have hwR : w∈R⊓centralizer (R : Set G) :=
    (le_sup_right.trans (source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS).2.le) hwZ
  have hwU : w∈sourceModule L :=
    ((source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge hwR).1
  have hcore : (pCore 2 L).map L.subtype=sourceModule L := by
    rw [source_block_core_eq_module d hG T hST hsingle]
    rfl
  obtain ⟨w',hw',hwval⟩ := hcore.ge hwU
  let v : pCore 2 L := ⟨w',hw'⟩
  have hv1 : v≠1 := by
    intro he
    have hh : w=1 := hwval.symm.trans (congrArg (fun t : pCore 2 L => ((t : L) : G)) he)
    exact hz1 ((MulAut.conj x⁻¹).injective (hh.trans (map_one _).symm))
  have hvf := source_outside_center_singular_of_normalizes_hall d hG T hST hsingle hL hM hTM hunique
    c hz x hxT hxS hxB e v (by
      change L.subtype w' ∈ _
      rw [hwval]
      exact hwZ)
  obtain ⟨l,hl⟩ := e.singular_conjugate v u hvf hv1 hu hu1
  have hzw : IsConj z ((v : L) : G) := isConj_iff.mpr ⟨x⁻¹,by
    change w=((v : L) : G)
    exact hwval.symm⟩
  exact hzw.trans (isConj_iff.mpr ⟨l.val,congrArg (fun t : pCore 2 L => ((t : L) : G)) hl⟩)

end CFSG.Quasithin.Chapter2.LinearShadows.Single
