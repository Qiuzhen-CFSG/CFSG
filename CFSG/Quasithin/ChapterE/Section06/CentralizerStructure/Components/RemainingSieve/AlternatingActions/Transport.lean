module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import Theory.ElementaryAbelian.Quotient

/-!
# From the faithful component action to ambient hyperplanes

Restricting conjugation gives the actual image of V in Aut(L); its kernel is
C_V(L). The image fixes a Sylow two-subgroup of L pointwise. Its order therefore
measures exactly the source action corank, without replacing the action by a
family label.

If that image has order four, each nonidentity cyclic subgroup pulls back to
a hyperplane of V containing U. Fixed points of the generator centralize this
whole preimage. Consequently, intrinsic fixed-point generation in L gives the
precise ambient hyperplane-generation assertion used in E.6.8(4).

These are transport lemmas. The six- and seven-letter action-image bounds and
fixed-point generation are separate model calculations, not asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247--248, especially the displayed generation identity on p.248.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
variable {G : Type*} [Group G] {V U L : Subgroup G}

/-- Fixed points of one actual automorphism, inside the group acted upon. -/
def fixedSubgroup {X : Type*} [Group X] (α : MulAut X) : Subgroup X :=
  α.toMonoidHom.eqLocus (MonoidHom.id X)

/-- Restrict ambient conjugation to a normalized component. -/
def actionHom (hn : V ≤ normalizer (L : Set G)) : V →* MulAut L :=
  L.normalizerMonoidHom.comp (inclusion hn)

@[simp] theorem actionHom_apply (hn : V ≤ normalizer (L : Set G)) (v : V) (x : L) :
    (actionHom hn v x : G) = (v : G) * (x : G) * (v : G)⁻¹ := rfl

/-- Its kernel is precisely the source fixed space C_V(L). -/
theorem actionHom_ker (hn : V ≤ normalizer (L : Set G)) :
    (actionHom hn).ker = (V ⊓ centralizer (L : Set G)).subgroupOf V := by
  ext v
  change actionHom hn v = 1 ↔ _
  constructor
  · intro hv
    refine ⟨v.property, ?_⟩
    intro x hx
    have hh := congrArg (fun a : MulAut L => (a ⟨x, hx⟩ : G)) hv
    change (v : G) * x * (v : G)⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hv
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (v : G) * (x : G) * (v : G)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 (x : G) x.property).symm

/-- The quotient dimension equals the logarithm of the actual action-image order. -/
theorem actionCorank_eq_log_card_range (hn : V ≤ normalizer (L : Set G)) :
    actionCorank V L = Nat.log 2 (Nat.card (actionHom hn).range) := by
  change Nat.log 2 ((V ⊓ centralizer (L : Set G)).subgroupOf V).index = _
  rw [← actionHom_ker hn, index_ker]

theorem actionCorank_le_two_of_card_range_le_four
    (hn : V ≤ normalizer (L : Set G)) (hc : Nat.card (actionHom hn).range ≤ 4) :
    actionCorank V L ≤ 2 := by
  rw [actionCorank_eq_log_card_range hn]
  exact (Nat.log_mono_right hc).trans (by decide)

/-- A marked ambient conjugation is literally in the faithful action image. -/
theorem mem_range_of_action {z : G} (hz : z ∈ V)
    (hn : V ≤ normalizer (L : Set G)) (α : MulAut L)
    (ha : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹) :
    α ∈ (actionHom hn).range := by
  refine ⟨⟨z, hz⟩, ?_⟩
  ext x
  exact (ha x).symm

/-- Elementary abelianness passes to this image, with no faithfulness premise. -/
theorem range_elementary [IsElementaryAbelian 2 V]
    (hn : V ≤ normalizer (L : Set G)) :
    IsElementaryAbelian 2 (actionHom hn).range :=
  IsElementaryAbelian.of_surjective _ (actionHom hn).rangeRestrict_surjective

/-- The component Sylow subgroup is fixed pointwise by every induced automorphism. -/
theorem exists_sylow_fixed_by_range [Finite G] {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : V ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 L, ∀ a ∈ (actionHom hn).range, ∀ x ∈ (S : Subgroup L), a x = x := by
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  refine ⟨S, ?_⟩
  rintro a ⟨v, rfl⟩ x hx
  apply Subtype.ext
  change (v : G) * (x : G) * (v : G)⁻¹ = x
  have hxQ : (x : G) ∈ sylowCentralizer (T : Subgroup G) V :=
    (hS ▸ mem_map_of_mem L.subtype hx).2
  rw [mem_centralizer_iff.mp hxQ.2 (v : G) v.property, mul_inv_cancel_right]

/-- Rank two gives an action image of order four, not merely an abstract rank tag. -/
theorem card_range_eq_four_of_actionCorank_two [Finite G] [IsElementaryAbelian 2 V]
    (hn : V ≤ normalizer (L : Set G)) (hd : actionCorank V L = 2) :
    Nat.card (actionHom hn).range = 4 := by
  rw [← index_ker, actionHom_ker hn]
  change (V ⊓ centralizer (L : Set G)).relIndex V = 4
  rw [relIndex_eq_two_pow_quotient_finrank,
    ← subgroupCorank_eq_quotient_finrank]
  change 2 ^ actionCorank V L = 4
  rw [hd]
  decide

/-- Pull back one line in the faithful image to an actual subgroup of V. -/
def linePreimage (hn : V ≤ normalizer (L : Set G))
    (a : (actionHom hn).range) : Subgroup G :=
  ((zpowers a).comap (actionHom hn).rangeRestrict).map V.subtype

theorem linePreimage_le (hn : V ≤ normalizer (L : Set G))
    (a : (actionHom hn).range) : linePreimage hn a ≤ V :=
  map_subtype_le _

theorem le_linePreimage (hn : V ≤ normalizer (L : Set G))
    (hUV : U ≤ V) (hLC : L ≤ centralizer (U : Set G))
    (a : (actionHom hn).range) : U ≤ linePreimage hn a := by
  intro u hu
  refine mem_map.mpr ⟨⟨u, hUV hu⟩, ?_, rfl⟩
  have huC := (le_centralizer_iff.mpr hLC) hu
  have he : actionHom hn ⟨u, hUV hu⟩ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [actionHom_ker hn]
    exact ⟨hUV hu, huC⟩
  change (actionHom hn).rangeRestrict ⟨u, hUV hu⟩ ∈ zpowers a
  have he' : (actionHom hn).rangeRestrict ⟨u, hUV hu⟩ = 1 := Subtype.ext he
  rw [he']
  exact one_mem _

/-- A nonidentity element of an elementary four-group spans an index-two line. -/
theorem linePreimage_corank [IsElementaryAbelian 2 V]
    (hn : V ≤ normalizer (L : Set G)) (hc : Nat.card (actionHom hn).range = 4)
    (a : (actionHom hn).range) (ha : a ≠ 1) :
    subgroupCorank V (linePreimage hn a) = 1 := by
  let _ := range_elementary hn
  have hao : orderOf a = 2 := by
    have hp : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (actionHom hn).range) a
    exact (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hp) |>.resolve_left
      (fun he => ha (orderOf_eq_one_iff.mp he))
  have hca : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers, hao]
  have hi : (zpowers a).index = 2 := by
    have hh := (zpowers a).card_mul_index
    rw [hca, hc] at hh
    omega
  have hrel : (linePreimage hn a).relIndex V = 2 := by
    change (((zpowers a).comap (actionHom hn).rangeRestrict).map V.subtype).relIndex V = 2
    conv_rhs => rw [← hi]
    have htop : (⊤ : Subgroup V).map V.subtype = V := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    conv_lhs => rhs; rw [← htop]
    rw [relIndex_map_map_of_injective _ _ V.subtype_injective]
    rw [relIndex_top_right, index_comap_of_surjective _ (actionHom hn).rangeRestrict_surjective]
  change Nat.log 2 ((linePreimage hn a).relIndex V) = 1
  rw [hrel]
  decide

/-- Fixed points of the line generator centralize its full ambient preimage. -/
theorem fixedSubgroup_le_centralizer_linePreimage
    (hn : V ≤ normalizer (L : Set G)) (a : (actionHom hn).range) :
    (fixedSubgroup (a : MulAut L)).map L.subtype ≤
      L ⊓ centralizer (linePreimage hn a : Set G) := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y.property, ?_⟩
  rintro v ⟨w, hw, rfl⟩
  let F : Subgroup (actionHom hn).range :=
    (MulAction.stabilizer (MulAut L) y).comap (actionHom hn).range.subtype
  have haF : a ∈ F := hy
  have hwF : (actionHom hn).rangeRestrict w ∈ F := (zpowers_le.mpr haF) hw
  have he : actionHom hn w y = y := hwF
  have hh := congrArg Subtype.val he
  change (w : G) * (y : G) * (w : G)⁻¹ = y at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Intrinsic fixed-point generation gives precisely the ambient hyperplane
family required by E.6.8, including the condition that every hyperplane contains U. -/
theorem hyperplane_generation_of_fixedSubgroup_generation [IsElementaryAbelian 2 V]
    (hn : V ≤ normalizer (L : Set G))
    (hUV : U ≤ V) (hLC : L ≤ centralizer (U : Set G))
    (hc : Nat.card (actionHom hn).range = 4)
    (hgen : (⊤ : Subgroup L) ≤ ⨆ (a : (actionHom hn).range) (_ : a ≠ 1),
      fixedSubgroup (a : MulAut L)) :
    L ≤ ⨆ (A : Subgroup G) (_ : U ≤ A) (_ : A ≤ V)
      (_ : subgroupCorank V A = 1), L ⊓ centralizer (A : Set G) := by
  have htop : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  conv_lhs => rw [← htop]
  apply map_le_iff_le_comap.mpr
  apply hgen.trans
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  apply map_le_iff_le_comap.mp
  exact (fixedSubgroup_le_centralizer_linePreimage hn a).trans
    (le_iSup_of_le (linePreimage hn a)
      (le_iSup_of_le (le_linePreimage hn hUV hLC a)
        (le_iSup_of_le (linePreimage_le hn a)
          (le_iSup_of_le (linePreimage_corank hn hc a ha) le_rfl))))

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
