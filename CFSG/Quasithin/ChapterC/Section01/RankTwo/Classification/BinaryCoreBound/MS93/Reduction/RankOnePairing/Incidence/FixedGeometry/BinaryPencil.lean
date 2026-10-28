module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.Values

/-!
# Recovering the binary seed and neighboring decompositions

Assume the value-space geometry in the fixed case of MS93 (1.7). The
irreducibility of Z kills the commutator image of each element of C ∩ Y,
because the local pairing image lies in a proper fixed space. The actual
coordinate map on Y has kernel C ∩ Y and image the binary two-space.

The image of X cannot be that whole space: this would put the commutator
values of a moving conjugate of X in two disjoint value lines. A proper
subgroup of the binary two-space is cyclic, giving an actual generator in
X modulo C. Finally, disjoint nonzero value lines force distinct seed
images, and any two nonzero distinct subgroups of the binary two-space
span it. Lifting this equality constructs the two required decompositions.

No rank-one marking is identified with the marking on Z, and no quotient
of W is assumed cyclic. Source: Meierfrankenfeld--Stellmacher (1993),
(1.7)(i), printed p.847.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
open Subgroup
universe u
variable {M : Type u} [Group M]

private abbrev Plane := Multiplicative (Fin 2 → ZMod 2)

private theorem plane_four : ∀ u v : Plane, u ≠ 1 → v ≠ 1 → u ≠ v →
    ∀ w : Plane, w = 1 ∨ w = u ∨ w = v ∨ w = u * v := by
  change ∀ u v : Fin 2 → ZMod 2, u ≠ 0 → v ≠ 0 → u ≠ v →
    ∀ w, w = 0 ∨ w = u ∨ w = v ∨ w = u + v
  decide

private theorem plane_span {A : Subgroup Plane} {u v : Plane}
    (hu : u ∈ A) (hv : v ∈ A) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    A = ⊤ := by
  apply top_unique
  intro w _
  rcases plane_four u v hu1 hv1 huv w with rfl | rfl | rfl | rfl
  · exact A.one_mem
  · exact hu
  · exact hv
  · exact A.mul_mem hu hv

private theorem proper_plane_cyclic (A : Subgroup Plane) (hA : A ≠ ⊤) :
    ∃ u ∈ A, ∀ v ∈ A, v = 1 ∨ v = u := by
  by_cases hz : A = ⊥
  · refine ⟨1, A.one_mem, ?_⟩
    intro v hv
    exact Or.inl (mem_bot.mp (hz ▸ hv))
  · obtain ⟨u, hu, hu1⟩ := A.bot_or_exists_ne_one.resolve_left hz
    refine ⟨u, hu, ?_⟩
    intro v hv
    by_cases hv1 : v = 1
    · exact Or.inl hv1
    · right
      by_contra hvu
      exact hA (plane_span hu hv hu1 hv1 (Ne.symm hvu))

private theorem distinct_plane_lines (A B : Subgroup Plane)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hAB : A ≠ B) : A ⊔ B = ⊤ := by
  by_contra htop
  obtain ⟨u, hu, hall⟩ := proper_plane_cyclic (A ⊔ B) htop
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  obtain ⟨b, hb, hb1⟩ := B.bot_or_exists_ne_one.resolve_left hB
  have hau := (hall a (mem_sup_left ha)).resolve_left ha1
  have hbu := (hall b (mem_sup_right hb)).resolve_left hb1
  apply hAB
  ext v
  constructor
  · intro hv
    rcases hall v (mem_sup_left hv) with rfl | rfl
    · exact B.one_mem
    · exact hbu ▸ hb
  · intro hv
    rcases hall v (mem_sup_right hv) with rfl | rfl
    · exact A.one_mem
    · exact hau ▸ ha

private theorem lift_image_le {E : Type*} [Group E]
    (Y C A B : Subgroup M) (q : Y →* E) (hk : q.ker = C.subgroupOf Y)
    (hAY : A ≤ Y)
    (h : (A.subgroupOf Y).map q ≤ (B.subgroupOf Y).map q) :
    A ≤ B ⊔ (C ⊓ Y) := by
  intro a ha
  obtain ⟨b, hb, he⟩ := h (mem_map_of_mem q (show (⟨a, hAY ha⟩ : Y) ∈ A.subgroupOf Y from ha))
  have hc : b⁻¹ * ⟨a, hAY ha⟩ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [hk] at hc
  have hm := (B ⊔ (C ⊓ Y)).mul_mem (mem_sup_left hb)
    (mem_sup_right (show (b : M)⁻¹ * a ∈ C ⊓ Y from
      ⟨hc, Y.mul_mem (Y.inv_mem b.property) (hAY ha)⟩))
  simpa only [subtype_apply, mul_inv_cancel_left] using hm

private theorem conjugate_le_of_normalized (A Y : Subgroup M) (hAY : A ≤ Y)
    {g : M} (hg : g ∈ normalizer (Y : Set M)) : conjugate g A ≤ Y := by
  rintro y ⟨a, ha, rfl⟩
  exact (mem_normalizer_iff.mp hg a).mp (hAY ha)

private theorem conjugate_commutator_ne_bot (A W : Subgroup M) [W.Normal]
    (h : ⁅A, W⁆ ≠ ⊥) (g : M) : ⁅conjugate g A, W⁆ ≠ ⊥ := by
  have he : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [conjugate, ← he, ← map_commutator]
  intro hz
  apply h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hz

variable [Finite M] {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
  [Z.Normal] [W.Normal]

/-- The actual rank-one quotient recovers the generator and both spans from
the value geometry, without a centralizer-propagation premise. -/
theorem seed_and_neighbors (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (v : ValueGeometry e i Z W X) :
    (∃ x : X, X ≤ zpowers (x : M) ⊔ fixedPreimage (component e.projection e.flag) X Z) ∧
    ∃ a b : M, a ∈ localParabolic e (!i) ∧ b ∈ localParabolic e (!i) ∧
      localGenerated (localParabolic e (!i)) X ≤
        (X ⊔ conjugate a X) ⊔
          (fixedPreimage (component e.projection e.flag) X Z ⊓
            localGenerated (localParabolic e (!i)) X) ∧
      localGenerated (localParabolic e (!i)) X ≤
        (X ⊔ conjugate b X) ⊔
          (fixedPreimage (component e.projection e.flag) X Z ⊓
            localGenerated (localParabolic e (!i)) X) ∧
      conjugate a (localFixed e Z i) ⊓ conjugate b (localFixed e Z i) = ⊥ := by
  let U := generated X
  let C := fixedPreimage (component e.projection e.flag) X Z
  let Y := localGenerated (localParabolic e (!i)) X
  let R := localParabolic e (!i)
  let D := localFixed e Z i
  let q : Y →* Plane := d.rank_one_natural.coordinates
  let image (A : Subgroup M) := (A.subgroupOf Y).map q
  have hk : q.ker = C.subgroupOf Y := d.rank_one_natural.kernel
  have hXY : X ≤ Y := le_localGenerated R X (d.x_le.trans (f.core_le (!i)))
  have hYU : Y ≤ U := localGenerated_le_generated R X
  have hXU : X ≤ U := le_normalClosure
  have hCYU : C ⊓ Y ≤ U := inf_le_right.trans hYU
  have hCY : C ⊓ Y ≤ centralizer (W : Set M) :=
    fixed_local_centralizes U W Z C (component e.projection e.flag) Y
      d.generated_commutator (f.z_central_W d) inf_le_left
      (fixedPreimage_commutator _ X Z) f.z_irreducible
      (fun h => v.local_proper (h.trans v.local_bound))
  have hCYW : ⁅C ⊓ Y, W⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hCY
  have hXW : ⁅X, W⁆ ≠ ⊥ := by
    intro he
    exact d.commutator_nontrivial (he ▸ card_bot)
  have hconj (g : M) (hg : g ∈ R) : conjugate g X ≤ Y :=
    conjugate_le_of_normalized X Y hXY (localGenerated_normalized R X hg)
  have himage (A : Subgroup M) (hAY : A ≤ Y) (hne : ⁅A, W⁆ ≠ ⊥) : image A ≠ ⊥ := by
    intro hz
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_trans ?_ hCY
    intro a ha
    have hv : q ⟨a, hAY ha⟩ ∈ image A := mem_map_of_mem q ha
    rw [hz, mem_bot] at hv
    have hc : (⟨a, hAY ha⟩ : Y) ∈ q.ker := hv
    rw [hk] at hc
    exact ⟨hc, hAY ha⟩
  obtain ⟨a, b, ha, hb, hDa, hDb, hab⟩ := v.value_neighbors
  have hproper : image X ≠ ⊤ := by
    intro ht
    have hspan : Y ≤ X ⊔ (C ⊓ Y) :=
      lift_image_le Y C Y X q hk le_rfl (by change image Y ≤ image X; rw [ht]; exact le_top)
    have hbnd : ⁅Y, W⁆ ≤ D := (commutator_mono hspan le_rfl).trans
      (pairing_sup_bound U W Z X (C ⊓ Y) D d.generated_commutator
        (f.z_central_generated d) hXU hCYU v.seed_bound (hCYW.le.trans bot_le))
    apply conjugate_commutator_ne_bot X W hXW a
    apply bot_unique
    rw [← hDa]
    exact le_inf ((commutator_mono (hconj a ha) le_rfl).trans hbnd)
      (commutator_conjugate_left X W D v.seed_bound a)
  have hspan (g : M) (hg : g ∈ R) (hDg : D ⊓ conjugate g D = ⊥) :
      Y ≤ (X ⊔ conjugate g X) ⊔ (C ⊓ Y) := by
    have hne : image X ≠ image (conjugate g X) := by
      intro he
      have hXg : X ≤ conjugate g X ⊔ (C ⊓ Y) :=
        lift_image_le Y C X (conjugate g X) q hk hXY he.le
      have hbnd : ⁅X, W⁆ ≤ conjugate g D := (commutator_mono hXg le_rfl).trans
        (pairing_sup_bound U W Z (conjugate g X) (C ⊓ Y) (conjugate g D)
          d.generated_commutator (f.z_central_generated d) ((hconj g hg).trans hYU) hCYU
          (commutator_conjugate_left X W D v.seed_bound g) (hCYW.le.trans bot_le))
      apply hXW
      exact bot_unique (hDg ▸ le_inf v.seed_bound hbnd)
    have ht : image (X ⊔ conjugate g X) = ⊤ := by
      change ((X ⊔ conjugate g X).subgroupOf Y).map q = ⊤
      rw [subgroupOf_sup hXY (hconj g hg), Subgroup.map_sup]
      exact distinct_plane_lines (image X) (image (conjugate g X))
        (himage X hXY hXW) (himage _ (hconj g hg) (conjugate_commutator_ne_bot X W hXW g)) hne
    exact lift_image_le Y C Y (X ⊔ conjugate g X) q hk le_rfl
      (by change image Y ≤ image (X ⊔ conjugate g X); rw [ht]; exact le_top)
  refine ⟨?_, a, b, ha, hb, hspan a ha hDa, hspan b hb hDb, hab⟩
  obtain ⟨u, hu, hall⟩ := proper_plane_cyclic (image X) hproper
  obtain ⟨x, hx, he⟩ := hu
  refine ⟨⟨x, hx⟩, ?_⟩
  apply (lift_image_le Y C X (zpowers (x : M)) q hk hXY ?_).trans
    (sup_le_sup_left inf_le_left _)
  intro t ht
  rcases hall t ht with rfl | rfl
  · exact one_mem _
  · exact he ▸ mem_map_of_mem q (show x ∈ (zpowers (x : M)).subgroupOf Y from mem_zpowers _)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
