module

public import CFSG.Quasithin.ChapterJ.Section05.SourceSeed
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Excluding the derived-Tits alternative in J.5.4

For the actual subgroup constructed in J.4, coprime commutator idempotence
puts Q₅ inside its derived subgroup. The original identity C_G(Q₅)=Z and
the native Tits center computation make that derived subgroup self-centralizing.
Its automorphism group has the order of the full Ree subgroup, so its
normalizer is precisely that subgroup. Consequently the intersection with
any distinct conjugate cannot contain the derived group.

This repairs the omitted index-two overgroup case in the numerical argument
of Aschbacher–Smith J.5.4, while preserving the original Q₅ and B₅ embeddings.
The equivalence with the full binary Ree group is the earlier J.4.7 input.
-/

public section
open Subgroup MulAction
open scoped commutatorElement
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

theorem Q₅_le_derived (B5 : Sylow 5 d.toTypeRuSetup.H) (F : Subgroup G)
    (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F) : Q₅ d B5 ≤ ⁅F,F⁆ := by
  let Q := d.toTypeRuSetup.Q
  let B := B5Image B5
  have hn : B ≤ normalizer (Q : Set G) := (map_subtype_le _).trans d.ru2.six.normalized
  let _ : Normalizes B Q := ⟨hn⟩
  have hs : Group.IsSolvable Q := by
    let := (isPGroup_pCoreIn 2 d.toTypeRuSetup.H).isNilpotent
    infer_instance
  have hc : Nat.Coprime (Nat.card B) (Nat.card Q) := by
    rw [B5Image_card d.card_Z B5,d.ru2.card_Q d.card_Z]
    decide
  have hi := commutatorAction₂_eq_commutatorAction_of_solvable_coprime
    (G := Q) (A := B) hs hc
  have hm := commutatorAction_subgroup_conj_map_eq_commutator Q B hn
  change ⁅Q,B⁆ ≤ _
  rw [← hm,← hi,commutatorAction₂,commutatorSubgroup,MonoidHom.map_closure,closure_le]
  rintro z ⟨q,⟨b,a,ha,rfl⟩,rfl⟩
  have haM : (a : G) ∈ Q₅ d B5 := by
    change (a : G) ∈ ⁅Q,B⁆
    rw [← hm]
    exact mem_map_of_mem Q.subtype ha
  have hh := commutator_mem_commutator (F.inv_mem (h5 haM)) (hB b.property)
  change (a : G)⁻¹ * ((b : G) * (a : G) * (b : G)⁻¹) ∈ ⁅F,F⁆
  simpa only [commutatorElement_def,inv_inv,mul_assoc] using hh

def sourceDerivedEquiv (F : Subgroup G) (e : F ≃* ReeF4.Model 0) :
    (⁅F,F⁆ : Subgroup G) ≃* Tits.Atlas1600Group :=
  (MulEquiv.subgroupCongr F.map_subtype_commutator.symm).trans
    ((equivMapOfInjective (commutator F) F.subtype F.subtype_injective).symm.trans
      ((e.subgroupMap (commutator F)).trans
        ((MulEquiv.subgroupCongr (by
          rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,← _root_.commutator_def])).trans
          atlasDerivedEquiv.symm)))

omit [Finite G] in
theorem source_derived_card (F : Subgroup G) (e : F ≃* ReeF4.Model 0) :
    Nat.card (⁅F,F⁆ : Subgroup G) = 17971200 :=
  (Nat.card_congr (sourceDerivedEquiv F e).toEquiv).trans Tits.atlas1600Group_card

theorem source_derived_centralizer (B5 : Sylow 5 d.toTypeRuSetup.H) (F : Subgroup G)
    (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F) (e : F ≃* ReeF4.Model 0) :
    centralizer ((⁅F,F⁆ : Subgroup G) : Set G) = ⊥ := by
  have hQD := Q₅_le_derived d B5 F h5 hB
  have hZ : d.toTypeRuSetup.Z ≤ ⁅F,F⁆ :=
    d.Z_le_V.trans ((le_conjugateSpan _ _).trans ((U_le_Q₅ d B5).trans hQD))
  have hC : centralizer ((⁅F,F⁆ : Subgroup G) : Set G) ≤ ⁅F,F⁆ :=
    ((centralizer_le hQD).trans_eq (centralizer_Q₅ d B5)).trans hZ
  apply bot_unique
  intro x hx
  let a : (⁅F,F⁆ : Subgroup G) := ⟨x,hC hx⟩
  have ha : a ∈ center (⁅F,F⁆ : Subgroup G) := by
    rw [mem_center_iff]
    intro b
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx b b.property
  have hz : sourceDerivedEquiv F e a ∈ center Tits.Atlas1600Group :=
    (centerCongr (sourceDerivedEquiv F e) ⟨a,ha⟩).property
  rw [Tits.RelativeSylowMarking.atlas_center_eq_bot,mem_bot] at hz
  have he : a = 1 := (sourceDerivedEquiv F e).injective (by simpa using hz)
  exact congrArg Subtype.val he

theorem source_derived_normalizer (B5 : Sylow 5 d.toTypeRuSetup.H) (F : Subgroup G)
    (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F) (e : F ≃* ReeF4.Model 0) :
    normalizer ((⁅F,F⁆ : Subgroup G) : Set G) = F := by
  have hF : F ≤ normalizer ((⁅F,F⁆ : Subgroup G) : Set G) := normalizer_commutator_ge_left F F
  have hi : Function.Injective (⁅F,F⁆ : Subgroup G).normalizerMonoidHom := by
    rw [← MonoidHom.ker_eq_bot_iff,normalizerMonoidHom_ker,
      source_derived_centralizer d B5 F h5 hB e]
    exact bot_subgroupOf _
  have hb := Nat.card_le_card_of_injective _ hi
  have hc : Nat.card (MulAut (⁅F,F⁆ : Subgroup G)) = Nat.card F := by
    rw [Nat.card_congr (MulAut.congr (sourceDerivedEquiv F e)).toEquiv,
      ← Nat.card_congr atlasAutEquiv.toEquiv,← Nat.card_congr e.toEquiv]
  exact (eq_of_le_of_card_ge hF (hc ▸ hb)).symm

theorem source_derived_not_le_conjugate (B5 : Sylow 5 d.toTypeRuSetup.H) (F : Subgroup G)
    (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F) (e : F ≃* ReeF4.Model 0)
    {g : G} (hg : g ∉ F) : ¬ ⁅F,F⁆ ≤ F.map (MulAut.conj g).toMonoidHom := by
  intro hD
  let K := F.map (MulAut.conj g).toMonoidHom
  have hK : Nat.card K = 35942400 := by
    rw [card_map_of_injective (MulAut.conj g).injective,Nat.card_congr e.toEquiv,group_card]
  have hdi : (⁅F,F⁆ : Subgroup G).relIndex K = 2 := by
    have hh := ((⁅F,F⁆ : Subgroup G).subgroupOf K).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv,source_derived_card F e,hK] at hh
    change 17971200 * (⁅F,F⁆ : Subgroup G).relIndex K = 35942400 at hh
    omega
  have hn : K ≤ normalizer ((⁅F,F⁆ : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hD).mp (normal_of_index_eq_two hdi)
  have hc : ⁅K,K⁆ ≤ ⁅F,F⁆ :=
    commutator_le_of_normalized_index_two K ⁅F,F⁆ K hD hdi K.le_normalizer hn
  have he : (⁅F,F⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⁅F,F⁆ := by
    apply eq_of_le_of_card_ge
    · rw [map_commutator]
      exact hc
    · rw [card_map_of_injective (MulAut.conj g).injective]
  have hgN := mem_normalizer_iff_map_conj_eq.mpr he
  rw [source_derived_normalizer d B5 F h5 hB e] at hgN
  exact hg hgN
end CFSG.Quasithin.ChapterJ.Section05
