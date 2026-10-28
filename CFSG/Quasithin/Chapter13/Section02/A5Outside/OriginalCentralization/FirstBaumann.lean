module
public import Stellmacher.BaumannWeakClosure
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BaumannFirst
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCenters
public import CFSG.Quasithin.ChapterB.Section02.BaumannCenter
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The first Baumann member in the original opposite-normalizer pair

The original alpha splitting places each natural module in Baum(T).
Thus the first characteristic-pair member lies in both literal local
two-cores. It is elementary of order two or four, and Baumann weak closure
makes it closed under ambient conjugacy into C_G(Baum(T)).

On the side normalizing that member, L=[L,J(T)] forces centralization.
Its nontrivial central seed cannot centralize the opposite component,
since the two components have trivial common Sylow centralizer. The
original omega splitting and irreducibility then show that its conjugate
span contains the opposite natural module. Both orientations are retained.

SourceAssembly/NonsolvableFirstBaumann applies this to the original
embedded O²(H) after every guarded rechoice. The opposite-normalizer
exclusion and the original generation lower bound remain to be proved.
Source: Aschbacher--Smith 13.2.4(2b),13.2.8(1), pp. 879--880;
C.1.18 and C.1.24(a), pp. 126,130--131; A.1.35, p. 30.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Subgroup Theory.GroupTheory Stellmacher ChapterB ChapterC Section05.A5Source
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The original natural module centralizes the full Thompson omega-center. -/
theorem original_module_le_baumann (d : Context T L V V₁ V₂ V₃) :
    V ≤ baumann (T : Subgroup G) := by
  refine le_inf d.chosen.le_sylow (le_centralizer_iff.mp ?_)
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)
  · exact (fun x hx => hJ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
  · rw [local_alpha_decomposition d hJ]
    let := d.elementary
    exact sup_le (inf_le_right.trans (centralizer_le d.chosen.le_component))
      (inf_le_left.trans (le_centralizer V))

/-- The first pair member lies in both actual local two-cores. -/
theorem original_first_baumann_le_cores
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G))) :
    D.first.map (baumann (T : Subgroup G)).subtype ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H.pCoreIn 2 := by
  let A := D.first.map (baumann (T : Subgroup G)).subtype
  have hAB : A ≤ baumann (T : Subgroup G) := map_subtype_le _
  have hAC : A ≤ centralizer (baumann (T : Subgroup G) : Set G) := by
    have h := GlaubermanNiles.image_centralizes_of_le_omegaCenter
      (baumann (T : Subgroup G)).subtype D.first D.first_le_omegaCenter
    rw [range_subtype] at h
    exact le_centralizer_iff.mp h
  rw [←d.sylow_centralizer d.normalizes_L,←hjoin,←e.sylow_centralizer e.normalizes_L]
  exact le_inf (le_inf (hAB.trans inf_le_left)
      (hAC.trans (centralizer_le (original_module_le_baumann d))))
    (le_inf (hAB.trans inf_le_left)
      (hAC.trans (centralizer_le (original_module_le_baumann e))))

/-- Conjugates of the first member in the Baumann centralizer stay in that member. -/
theorem first_baumann_fusion_closed
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    {x y : G} (hx : x ∈ D.first.map (baumann (T : Subgroup G)).subtype)
    (hy : y ∈ centralizer (baumann (T : Subgroup G) : Set G))
    (hxy : IsConj x y) : y ∈ D.first.map (baumann (T : Subgroup G)).subtype := by
  have hBC := GlaubermanNiles.image_centralizes_of_le_omegaCenter
    (baumann (T : Subgroup G)).subtype D.first D.first_le_omegaCenter
  rw [range_subtype] at hBC
  obtain ⟨n,hn,rfl⟩ := baumann_normalizer_controls_centralizer_fusion T
    (le_centralizer_iff.mp hBC hx) hy hxy
  let := D.first_characteristic
  exact (mem_normalizer_iff.mp
    (normalizer_le_normalizer_characteristic_image (baumann (T : Subgroup G)) D.first hn) x).mp hx

private theorem first_centralizes_component
    (d : Context T L V V₁ V₂ V₃)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer
      (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) :
    D.first.map (baumann (T : Subgroup G)).subtype ≤ centralizer (L : Set G) := by
  let A := D.first.map (baumann (T : Subgroup G)).subtype
  have hBC := GlaubermanNiles.image_centralizes_of_le_omegaCenter
    (baumann (T : Subgroup G)).subtype D.first D.first_le_omegaCenter
  rw [range_subtype] at hBC
  have hJC : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (A : Set G) :=
    (elementaryAbelianMaxJ_le_baumann _).trans hBC
  have hLN : L ≤ normalizer (centralizer (A : Set G) : Set G) :=
    (le_sup_left.trans hn).trans (normalizer_le_normalizer_centralizer A)
  apply le_centralizer_iff.mp
  rw [d.eq_thompson_commutator_of_moves hJ]
  exact (commutator_mono le_rfl hJC).trans
    ((commutator_comm L (centralizer (A : Set G))).le.trans
      (le_normalizer_iff_commutator_le_left.mp hLN))

/-- Either first-member normalization bounds its order by the original fixed alpha part. -/
theorem original_opposite_first_baumann_small
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer
        (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∨
      H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) :
    IsElementaryAbelian 2 (D.first.map (baumann (T : Subgroup G)).subtype) ∧
      (Nat.card (D.first.map (baumann (T : Subgroup G)).subtype) = 2 ∨
        Nat.card (D.first.map (baumann (T : Subgroup G)).subtype) = 4) := by
  let A := D.first.map (baumann (T : Subgroup G)).subtype
  have hAE : A ≤ thompsonAlpha (T : Subgroup G) := by
    rw [←omegaCenter_baumann_eq_thompsonAlpha]
    exact map_mono D.first_le_omegaCenter
  let : IsElementaryAbelian 2 (thompsonAlpha (T : Subgroup G)) :=
    omegaOneCenterAmbient_elementaryAbelian (elementaryAbelianMaxJ (T : Subgroup G))
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAE
  have hb := original_pair_alpha_bounds d e hH hjoin hJd hJe
  have hcard : Nat.card A ≤ 4 := by
    rcases hn with hn | hn
    · exact (card_le_of_le (le_inf hAE (first_centralizes_component d hJd D hn))).trans hb.2.1
    · rw [←hjoin] at hn
      exact (card_le_of_le (le_inf hAE (first_centralizes_component e hJe D hn))).trans hb.2.2
  have hne : A ≠ ⊥ := fun hh => D.first_ne_bot
    ((D.first.map_eq_bot_iff_of_injective (baumann (T : Subgroup G)).subtype_injective).mp hh)
  have hpos := A.one_lt_card_iff_ne_bot.mpr hne
  let := hA
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnot3 : Nat.card A ≠ 3 := by
    intro he
    rw [he] at hn
    have hd : 3 ∣ 2 ^ n := hn ▸ dvd_refl 3
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at this
  refine ⟨hA,?_⟩
  change Nat.card A = 2 ∨ Nat.card A = 4
  omega
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Subgroup Theory.GroupTheory Stellmacher ChapterB ChapterC Section05.A5Source
open scoped IsMulCommutative Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- A nontrivial elementary Sylow-normalized subgroup fixed by one original
component generates the opposite natural module from its central seed. -/
theorem opposite_module_le_fixed_seed_span
    (e : Context T K W W₁ W₂ W₃)
    (hcommon : (T : Subgroup G) ⊓ centralizer (L : Set G) ⊓
      centralizer (K : Set G) = ⊥)
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥)
    (hAT : A ≤ (T : Subgroup G)) (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hAL : A ≤ centralizer (L : Set G)) :
    W ≤ conjugateSpanBy (A ⊓ omegaOneCenterAmbient (T : Subgroup G)) K := by
  let C := A ⊓ omegaOneCenterAmbient (T : Subgroup G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (K : Set G)
  let U := conjugateSpanBy C K
  have hCne : C ≠ ⊥ := by
    have hne' := inf_centerIn_ne_bot T.isPGroup' hne hAT hTA
    intro hz
    apply hne'
    apply bot_unique
    intro x hx
    apply hz.le
    exact ⟨hx.1,(mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hAT hx.1,elemPow_eq_one_of_isElementaryAbelian x hx.1,hx.2.2⟩⟩
  have hmove : ¬ C ≤ centralizer (K : Set G) := by
    intro hh
    apply hCne
    apply bot_unique
    exact (le_inf (le_inf (inf_le_left.trans hAT) (inf_le_left.trans hAL)) hh).trans
      hcommon.le
  have hZW : Z ≤ W ⊔ F :=
    (omega_decomposition_of_thompson_moves e hJe).le.trans
      (sup_le_sup (e.flag.one_le_two.trans e.flag.two_le_V) le_rfl)
  have hUn : K ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy C K
  have hCW : ⁅C,K⁆ ≤ W := by
    apply commutator_le.mpr
    intro c hc k hk
    have hprod : c ∈ (W : Set G) * (F : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left W F
        ((inf_le_right.trans (centralizer_le e.chosen.le_component)).trans
          (Subgroup.centralizer_le_normalizer _))]
      exact hZW hc.2
    obtain ⟨w,hw,f,hf,rfl⟩ := hprod
    have hfk : k * f * k⁻¹ = f := mul_inv_eq_iff_eq_mul.mpr (hf.2 k hk)
    have heq : ⁅w*f,k⁆ = w * (k * w⁻¹ * k⁻¹) := by
      simp only [commutatorElement_def,mul_inv_rev]
      have hi : k * f⁻¹ * k⁻¹ = f⁻¹ := by
        simpa only [mul_inv_rev,inv_inv,mul_assoc] using congrArg Inv.inv hfk
      calc
        _ = w * (f * (k * f⁻¹ * k⁻¹)) * (k * w⁻¹ * k⁻¹) := by group
        _ = _ := by rw [hi,mul_inv_cancel,mul_one]
    rw [heq]
    exact W.mul_mem hw ((mem_normalizer_iff.mp (e.chosen.normalizes hk) _).mp (W.inv_mem hw))
  have hCU : ⁅C,K⁆ ≤ U :=
    (commutator_mono (le_conjugateSpanBy C K) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hUn)
  have hUWne : U ⊓ W ≠ ⊥ := by
    intro hh
    exact hmove (commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique ((le_inf hCU hCW).trans hh.le)))
  rcases e.irreducible_module (U ⊓ W) inf_le_right
      ((le_inf hUn e.chosen.normalizes).trans inf_normalizer_le_normalizer_inf) with hh | hh
  · exact (hUWne hh).elim
  · exact hh.ge.trans inf_le_left
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Subgroup Theory.GroupTheory Stellmacher ChapterB ChapterC Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The first member in either opposite-normalizer alternative is a small
common-core subgroup, closed under fusion into the Baumann centralizer.
Its central seed generates the natural module on the opposite side. -/
theorem original_first_baumann_structure
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer
        (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∨
      H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) :
    let A := D.first.map (baumann (T : Subgroup G)).subtype
    A ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H.pCoreIn 2 ∧
      IsElementaryAbelian 2 A ∧ (Nat.card A = 2 ∨ Nat.card A = 4) ∧
      ((A ≤ centralizer (L : Set G) ∧
          W ≤ conjugateSpanBy (A ⊓ omegaOneCenterAmbient (T : Subgroup G)) K) ∨
        (A ≤ centralizer (K : Set G) ∧
          V ≤ conjugateSpanBy (A ⊓ omegaOneCenterAmbient (T : Subgroup G)) L)) ∧
      ∀ x ∈ A, ∀ y ∈ centralizer (baumann (T : Subgroup G) : Set G),
        IsConj x y → y ∈ A := by
  let A := D.first.map (baumann (T : Subgroup G)).subtype
  obtain ⟨hA,hcard⟩ := original_opposite_first_baumann_small d e hjoin hH hJd hJe D hn
  let := hA
  have hne : A ≠ ⊥ := fun hh => D.first_ne_bot
    ((D.first.map_eq_bot_iff_of_injective (baumann (T : Subgroup G)).subtype_injective).mp hh)
  have hAT : A ≤ (T : Subgroup G) := (map_subtype_le _).trans inf_le_left
  let := D.first_characteristic
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ D.first)
  have hcommon := common_sylow_centralizer_eq_bot d hH e.normalizes_L hjoin
  refine ⟨original_first_baumann_le_cores d e hjoin D,hA,hcard,?_,
    fun _ hx _ hy hxy => first_baumann_fusion_closed D hx hy hxy⟩
  rcases hn with hn | hn
  · have hAL := first_centralizes_component d hJd D hn
    exact Or.inl ⟨hAL,opposite_module_le_fixed_seed_span e hcommon hJe A hne hAT hTA hAL⟩
  · rw [←hjoin] at hn
    have hAK := first_centralizes_component e hJe D hn
    have hcommon' : (T : Subgroup G) ⊓ centralizer (K : Set G) ⊓ centralizer (L : Set G) = ⊥ := by
      simpa only [inf_assoc,inf_comm,inf_left_comm] using hcommon
    exact Or.inr ⟨hAK,opposite_module_le_fixed_seed_span d hcommon' hJd A hne hAT hTA hAK⟩
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
