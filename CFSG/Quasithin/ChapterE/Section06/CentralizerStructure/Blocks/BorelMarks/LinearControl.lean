module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelMarks.LinearNormalizer
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.ElementaryThompsonFrattini
/-!
# Full Sylow-normalizer control for an original linear block

Intersect the original Sylow subgroup with the block normalizer. The movement
equation puts the original Thompson subgroup in this intersection, so its
Thompson subgroup remains unchanged. The natural-module normalizer theorem
then puts the full block Sylow normalizer in N(J(S)), hence in the prescribed
characteristic-normalizer overgroup. The Sylow subgroup of the normalized
extension is constructed from the original subnormal intersection.

Source: Aschbacher–Smith C.1.29, printed p.134, applied in E.6.7, p.246.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.ChapterE.Section06
open ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem linear_block_sylow_normalizer_le_control
    (S : Sylow 2 G) (N K : Subgroup G)
    (hcontrol : (S : Subgroup G).characteristicNormalizerClosure ≤ N)
    (hout : ¬K ≤ N) (hmove : K = ⁅K,Stellmacher.elementaryAbelianMaxJ (S : Subgroup G)⁆)
    {n : ℕ} (htype : IsL2EvenBlock K n)
    (Z : Sylow 2 K) (hZ : (Z : Subgroup K).map K.subtype = K ⊓ S) :
    normalizer (Z : Set K) ≤ N.subgroupOf K := by
  let T := (S : Subgroup G) ⊓ normalizer (K : Set G)
  have hJT : elementaryAbelianMaxJ (S : Subgroup G) ≤ T := by
    apply le_inf (sSup_le fun _ hA => hA.1)
    exact le_normalizer_iff_commutator_le_left.mpr hmove.ge
  have hJ : elementaryAbelianMaxJ T = elementaryAbelianMaxJ (S : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ T hJT inf_le_left
  have hT : IsPGroup 2 T := S.isPGroup'.to_le inf_le_left
  have hn : T ≤ normalizer (K : Set G) := inf_le_right
  have hZT : (Z : Subgroup K).map K.subtype ≤ T := by
    rw [hZ]
    exact le_inf inf_le_right (inf_le_left.trans K.le_normalizer)
  obtain ⟨P,hP⟩ := hT.exists_sylow_sup_of_coprime_index K T hn (Z : Subgroup K)
    Z.not_dvd_index hZT
  have hKT : K ⊓ T = K ⊓ S := by
    ext x
    exact ⟨fun hx => ⟨hx.1,hx.2.1⟩,fun hx => ⟨hx.1,hx.2,K.le_normalizer hx.1⟩⟩
  obtain ⟨hnlarge,hshort,F,_,_,hF,_,τ,⟨m⟩,hτ⟩ := htype
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hlarge : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    rw [hF]
    norm_num at hh ⊢
    omega
  have hlift := natural_sylow_normalizer_preserves_thompson K T hshort hT hn P hP
    (by rwa [hJ]) τ m hτ hlarge
  have hJne : elementaryAbelianMaxJ (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    have hk : K = ⊥ := by simpa only [hbot,commutator_bot_right] using hmove
    exact hout (hk ▸ bot_le)
  have hNM : normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G) ≤ N :=
    (normalizer_maxJ_le_characteristicNormalizerClosure (S : Subgroup G) (S : Subgroup G)
      (sSup_le fun _ hA => hA.1) le_rfl hJne).trans hcontrol
  intro z hz
  have hzn : (z : G) ∈ normalizer (↑(K ⊓ T) : Set G) := by
    rw [hKT,←hZ]
    exact (Z : Subgroup K).le_normalizer_map K.subtype (mem_map_of_mem K.subtype hz)
  exact hNM (hJ ▸ hlift ⟨z.property,hzn⟩)

end CFSG.Quasithin.ChapterE.Section06
