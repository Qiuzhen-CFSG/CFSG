module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.OddMover
/-!
# The moving hyperplane in the natural branch of 13.3.14(b)

The actual natural A₆ pairing identifies V₃ with V₁-perpendicular.
An element of L moving V₁ therefore moves V₃. The two distinct hyperplanes
then generate the original four-dimensional V. Combining this with the
cubic plane-action lift chooses an odd-order element of the same source
parabolic; central covers and the actual conjugation maps are retained.

Source: Aschbacher–Smith, 13.3.14(b), printed p.891. This supplies the
geometric mover used in the conjugate-intersection argument, without
assuming either that intersection or the subsequent rank conclusions.
-/

@[expose] public noncomputable section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d
private theorem image_injective_on (A B : Subgroup G) (hA : A ≤ V) (hB : B ≤ V)
    (he : image d A = image d B) : A = B := by
  apply le_antisymm
  · intro a ha
    have hm : (d.coordinate ⟨a,hA ha⟩).toAdd ∈ image d B := he ▸ ⟨⟨a,hA ha⟩,ha,rfl⟩
    obtain ⟨b,hb,hba⟩ := hm
    have hh := congrArg (fun v : V => v.val) (d.coordinate.injective hba)
    change b.val = a at hh
    exact hh ▸ hb
  · intro b hb
    have hm : (d.coordinate ⟨b,hB hb⟩).toAdd ∈ image d A := he.symm ▸ ⟨⟨b,hB hb⟩,hb,rfl⟩
    obtain ⟨a,ha,hab⟩ := hm
    have hh := congrArg (fun v : V => v.val) (d.coordinate.injective hab)
    change a.val = b at hh
    exact hh ▸ ha
private theorem image_conjugate (A : Subgroup G) (hA : A ≤ V) (g : L) :
    image d (A.map (MulAut.conj g.val).toMonoidHom) =
      (image d A).map (naturalRepresentation (Fin 6)
        (d.local_quotient (QuotientGroup.mk' _ g)).val) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨v,⟨a,ha,hav⟩,rfl⟩ := hw
    refine ⟨(d.coordinate ⟨a,hA ha⟩).toAdd,⟨⟨a,hA ha⟩,ha,rfl⟩,?_⟩
    have hh := d.conjugation g ⟨a,hA ha⟩
    have he : V.normalizerMonoidHom ⟨g.val,d.normalizes_V (mem_sup_left g.property)⟩
        ⟨a,hA ha⟩ = v := Subtype.ext hav
    rw [he] at hh
    exact hh.symm
  · rintro _ ⟨w,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨V.normalizerMonoidHom ⟨g.val,d.normalizes_V (mem_sup_left g.property)⟩ v,
      ⟨v.val,hv,rfl⟩,d.conjugation g v⟩
private theorem conjugate_le_V (A : Subgroup G) (hA : A ≤ V) (g : L) :
    A.map (MulAut.conj g.val).toMonoidHom ≤ V := by
  rintro _ ⟨a,ha,rfl⟩
  exact (mem_normalizer_iff.mp (d.normalizes_V (mem_sup_left g.property)) a).mp (hA ha)
private theorem seed_moved (g : L) (hg : g.val ∉ normalizer (P : Set G)) :
    U.map (MulAut.conj g.val).toMonoidHom ≠ U := by
  intro he
  apply hg
  have him := congrArg (image d) he
  rw [image_conjugate d U d.seed_le g] at him
  have hp := orthogonal_invariant (image d U) _ him
  have hor : form.orthogonal (image d U) = image d P := by
    rw [seed_perpendicular d,LinearMap.BilinForm.orthogonal_orthogonal
      form_nondegenerate form_alt.isRefl]
  rw [hor] at hp
  apply (mem_normalizer_iff_map_conj_eq).mpr
  apply image_injective_on d _ P (conjugate_le_V d P
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) g)
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
  rw [image_conjugate d P (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) g]
  exact hp
/-- A point-moving element of the original L generates V from two seed conjugates. -/
theorem natural_seed_join_of_point_moved (g : L) (hg : g.val ∉ normalizer (P : Set G)) :
    U ⊔ U.map (MulAut.conj g.val).toMonoidHom = V := by
  let W := U.map (MulAut.conj g.val).toMonoidHom
  let J := U ⊔ W
  have hWV : W ≤ V := conjugate_le_V d U d.seed_le g
  have hJV : J ≤ V := sup_le d.seed_le hWV
  have hcardV : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_eq_fintype_card,ZMod.card,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have hWcard : Nat.card W = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g.val).injective,d.seed_card]
  have hneq : W ≠ U := seed_moved d g hg
  have hUJ : U < J := lt_of_le_of_ne le_sup_left (by
    intro he
    apply hneq
    exact eq_of_le_of_card_ge (he ▸ (show W ≤ J from le_sup_right)) (by rw [d.seed_card,hWcard]))
  have hlo : 8 < Nat.card J := by
    rw [← d.seed_card]
    have hle := Nat.card_le_card_of_injective _ (inclusion_injective hUJ.le)
    exact lt_of_le_of_ne hle (fun he => hUJ.ne (eq_of_le_of_card_ge hUJ.le he.ge))
  let := d.chosen.elementary
  obtain ⟨n,hn⟩ := ((IsElementaryAbelian.isPGroup 2 V).to_le hJV).exists_card_eq
  have hhi : Nat.card J ≤ 16 := by
    rw [← hcardV]
    exact Nat.card_le_card_of_injective _ (inclusion_injective hJV)
  rw [hn] at hlo hhi
  have hnlo : 3 < n := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlo
  have hnhi : n ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hhi
  have hn4 : n = 4 := by omega
  exact eq_of_le_of_card_ge hJV (by rw [hn,hn4,hcardV]; decide)
/-- Choose the actual odd parabolic mover and its two generating hyperplanes. -/
theorem natural_odd_plane_mover (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Section05.AmbientSource.planeAction E)) = 3) :
    ∃ g : G, g ∈ X ∧ Odd (orderOf g) ∧ g ∈ normalizer (E : Set G) ∧
      g ∉ normalizer (P : Set G) ∧ U ⊔ U.map (MulAut.conj g).toMonoidHom = V := by
  let := Section05.AmbientSource.source_plane_isKleinFour d
  obtain ⟨g,hg,ho,hn,hm⟩ := exists_odd_plane_mover P E X d.line_card d.line_le_plane hx
  exact ⟨g,hg,ho,hn,hm,natural_seed_join_of_point_moved d ⟨g,hXL hg⟩ hm⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
