module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.PowerAction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Automizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear

/-!
# The G₂ pair action after Sylow and torus placement

Inner–field coverage and preservation of the positive-root Sylow subgroup
force the inner factor into its Borel normalizer. For a subgroup of the
split torus, the Borel factor then centralizes the subgroup. Coefficient
transport supplies a uniform power formula, which is transported back along
an actual group isomorphism and descended to the Frattini quotient.

This controls the entire pair automizer, including all its two-subgroups.
The two remaining inputs are explicit: abstract automorphism coverage and
simultaneous placement of the Sylow subgroup and complement. Neither is
assumed in PairInput or claimed to follow from a family name here.

Source: Aschbacher–Smith Proposition 1.3.4, printed p.511 (PDF p.528).
The reused octonion computations are from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions

variable {F : Type*} [Field F] [CharP F 2]

/-- Every inner pair stabilizer acts trivially on a torus complement. -/
theorem g2_inner_kernel (B : Subgroup (Model F)) (hB : B ≤ splitTorus) :
    normalizer (unipotent (K := F) : Set (Model F)) ⊓ normalizer B ≤
      centralizer (B : Set (Model F)) := by
  rw [SylowNormalizer.normalizer_unipotent]
  exact InvariantLarge.EvenActions.G2.borel_kernel B hB

/-- Coverage and Sylow preservation put the actual inner factor in the Borel. -/
theorem g2_borel_field_of_sylow
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (a : MulAut (Model F))
    (ha : unipotent.map a.toMonoidHom = unipotent) :
    ∃ (d : Model F) (σ : F ≃+* F), d ∈ borel ∧
      a = MulAut.conj d * fieldEquiv σ := by
  obtain ⟨z, hz⟩ := hcover a
  have he : a = MulAut.conj z.left * fieldEquiv z.right := hz.symm
  refine ⟨z.left, z.right, ?_, he⟩
  rw [he] at ha
  change unipotent.map ((MulAut.conj z.left).toMonoidHom.comp
    (fieldEquiv z.right).toMonoidHom) = unipotent at ha
  rw [← map_map, SylowNormalizer.field_map_unipotent] at ha
  rw [← SylowNormalizer.normalizer_unipotent]
  exact mem_normalizer_iff_map_conj_eq.mpr ha

variable [Finite F]

/-- An actual automorphism preserving the Sylow and a torus subgroup acts by
one Frobenius power on that subgroup, with its inner factor in the kernel. -/
theorem g2_torus_pair_power
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (B : Subgroup (Model F)) (hB : B ≤ splitTorus)
    (a : MulAut (Model F))
    (haU : unipotent.map a.toMonoidHom = unipotent)
    (haB : B.map a.toMonoidHom = B) :
    ∃ k : ℕ, ∀ b ∈ B, a b = b ^ (2 ^ k) := by
  obtain ⟨d, σ, hd, he⟩ := g2_borel_field_of_sylow hcover a haU
  exact InvariantLarge.EvenActions.G2.borel_field_power B hB a haB d hd σ he

private theorem map_eq_of_mem_iff {G : Type*} [Group G] (H : Subgroup G)
    (a : MulAut G) (ha : ∀ x, a x ∈ H ↔ x ∈ H) : H.map a.toMonoidHom = H := by
  ext x
  obtain ⟨y, rfl⟩ := a.surjective x
  change a.toMonoidHom y ∈ H.map a.toMonoidHom ↔ a y ∈ H
  rw [mem_map_iff_mem a.injective, ha]

private theorem map_congr_aut {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a : MulAut G) (K : Subgroup G) :
    (K.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom =
      (K.map a.toMonoidHom).map e.toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

variable {Q : Type*} [Group Q]

/-- Simultaneous Sylow/torus coordinates control every extendible automorphism
of the original complement. No p > 3 hypothesis is used. -/
theorem g2_pair_power_of_equiv (S R : Subgroup Q) (e : Q ≃* Model F)
    (hS : S.map e.toMonoidHom = unipotent)
    (hR : R.map e.toMonoidHom ≤ splitTorus)
    (hcover : Function.Surjective (semilinearAction (F := F))) :
    ∀ b ∈ pairAutomizer S R, ∃ k : ℕ, ∀ r : R, b r = r ^ (2 ^ k) := by
  intro b hb
  obtain ⟨a, he⟩ := pairRestriction_surjective S R ⟨b, hb⟩
  have hab (r : R) : (b r : Q) = a.val r :=
    (congrArg (fun c : pairAutomizer S R => (c.val r : Q)) he).symm
  have haS := map_eq_of_mem_iff S a.val a.property.1
  have haR := map_eq_of_mem_iff R a.val a.property.2
  have hu : unipotent.map (MulAut.congr e a.val).toMonoidHom = unipotent := by
    rw [← hS, map_congr_aut, haS]
  have hr : (R.map e.toMonoidHom).map (MulAut.congr e a.val).toMonoidHom =
      R.map e.toMonoidHom := by
    rw [map_congr_aut, haR]
  obtain ⟨k, hk⟩ := g2_torus_pair_power hcover (R.map e.toMonoidHom) hR
    (MulAut.congr e a.val) hu hr
  refine ⟨k, fun r => Subtype.ext (e.injective ?_)⟩
  change e (b r : Q) = e ((r : Q) ^ (2 ^ k))
  rw [hab, map_pow]
  simpa [MulAut.congr_apply] using hk (e r) (mem_map_of_mem e.toMonoidHom r.property)

/-- The three-complement is reducible after the two genuine model inputs,
simultaneous placement and automorphism coverage, have been established. -/
theorem g2_pairReducible_of_equiv [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (e : Q ≃* Model F)
    (hS : (S : Subgroup Q).map e.toMonoidHom = unipotent)
    (hR : R.map e.toMonoidHom ≤ splitTorus)
    (hcover : Function.Surjective (semilinearAction (F := F))) :
    PairReducible (S : Subgroup Q) R := by
  apply pairReducible_of_powers _ _ h.oddComplement.not_isCyclic
  intro b hb
  obtain ⟨k, hk⟩ := g2_pair_power_of_equiv (S : Subgroup Q) R e hS hR hcover b hb
  exact ⟨2 ^ k, hk⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
