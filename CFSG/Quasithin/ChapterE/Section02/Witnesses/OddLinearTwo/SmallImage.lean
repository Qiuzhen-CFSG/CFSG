module
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.NonexceptionalSource
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PCoreLocalSetup
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original small image in the odd linear-two row

The actual core-free minimal parabolic has maximal subgroup C(t), where
t is an involution in the normal PSL₂ component. Adjoin t to the elementary
image W of V. The existing bound on normal elementary subgroups in O₂(M)
forces this join to have order at most two, so nontrivial W contains t and
has order two. Transport retains the literal quotient H/J and component
image, supplying the inverter used by the small-automizer exclusion.

Source: Aschbacher–Smith E.2.17, printed p.230, using E.2.2(2c).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses.OddLinearTwo
private theorem central_involution_mem_of_elementary_bound
    {G : Type*} [Group G] [Finite G] (T M W : Subgroup G)
    [IsElementaryAbelian 2 W] (hWT : W ≤ T) (hTW : T ≤ normalizer (W : Set G))
    (hWM : W ≤ M.pCoreIn 2) (hW : W ≠ ⊥)
    (t : G) (ht : orderOf t = 2) (htT : t ∈ T) (hTM : T ≤ M)
    (hM : M = centralizer ({t} : Set G))
    (hbound : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ T →
      T ≤ normalizer (A : Set G) → A ≤ M.pCoreIn 2 → Nat.card A ≤ 2) :
    t ∈ W ∧ Nat.card W = 2 := by
  let R := zpowers t
  have ht2 : t^2=1 := by simpa only [ht] using pow_orderOf_eq_one t
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  have hRC : M ≤ centralizer (R : Set G) := by
    rw [hM]
    intro x hx y hy
    obtain ⟨n,rfl⟩ := hy
    exact (Commute.zpow_right (show Commute x t from mem_centralizer_singleton_iff.mp hx) n).eq.symm
  have hRM : R ≤ M.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 R) ((zpowers_le.mpr htT).trans hTM)
    (hRC.trans (Subgroup.centralizer_le_normalizer _))
  have hWR : R ≤ centralizer (W : Set G) :=
    le_centralizer_iff.mp (((hWM.trans (pCoreIn_le 2 M)).trans hRC))
  let A := W ⊔ R
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.sup_of_le_centralizer hWR
  have hAT : A ≤ T := sup_le hWT (zpowers_le.mpr htT)
  have hTA : T ≤ normalizer (A : Set G) :=
    (le_inf hTW (hTM.trans (hRC.trans (Subgroup.centralizer_le_normalizer _)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup W R)
  have hAc : Nat.card A ≤ 2 := hbound A inferInstance hAT hTA (sup_le hWM hRM)
  have hWc : 2 ≤ Nat.card W := by have := (one_lt_card_iff_ne_bot W).mpr hW; omega
  have he : W = A := eq_of_le_of_card_ge le_sup_left (hAc.trans hWc)
  exact ⟨he ▸ (show t ∈ A from (show R ≤ A from le_sup_right) (mem_zpowers t)),
    le_antisymm ((card_le_of_le (show W ≤ A from le_sup_left)).trans hAc) hWc⟩

theorem corefree_odd_image_involution
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) [K.Normal] (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hO : pCore 2 G = ⊥) {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hn : n=1 ∨ n=2)
    (hF : Nat.card F = p^n) (hlarge : 9 < Nat.card F)
    (e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWT : W ≤ T) (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hWM : W ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) (hW : W ≠ ⊥) :
    Nat.card W = 2 ∧ ∃ t : K, orderOf t = 2 ∧ (t:G) ∈ W := by
  let M := ChapterB.minimalParabolicMax T hP
  have hc : ∃ t : K, GorensteinWalter.IsInvolution t ∧ (t:G) ∈ (T:Subgroup G) ∧
      (T:Subgroup G) ≤ centralizer ({(t:G)} : Set G) ∧
      M = centralizer ({(t:G)} : Set G) ∧
      M.subgroupOf K = centralizer ({t} : Set K) := by
    rcases hn with rfl | rfl
    · exact Structure.prime_linear_source_centralizer T hP K hgen ho
        (by simpa using hF) (by simpa [hF] using hlarge) e
    · exact Structure.quadratic_linear_source_centralizer T hP K hgen ho hF hp e
  obtain ⟨t,ht,htT,_,hM,_⟩ := hc
  have hb : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ T →
      (T : Subgroup G) ≤ normalizer (A : Set G) → A ≤ M.pCoreIn 2 → Nat.card A ≤ 2 := by
    intro A hA hAT hTA hAM
    rcases hn with rfl | rfl
    · exact Structure.prime_linear_source_elementary_card_le_two T hP K hgen hO ho
        (by simpa using hF) (by simpa [hF] using hlarge) e A hA hAT hTA
    · exact Structure.quadratic_linear_source_elementary_card_le_two T hP K hgen hO ho
        hF hp e A hA hAM hTA
  have htord : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  obtain ⟨htW,hc⟩ := central_involution_mem_of_elementary_bound (T:Subgroup G) M W
    hWT hTW hWM hW t (by simpa using htord) htT
    (ChapterB.minimalParabolicMax_spec T hP).2 hM hb
  exact ⟨hc,t,htord,htW⟩

theorem source_odd_image_involution
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p) (hn : n=1 ∨ n=2)
    (hlarge : 9 < p^n)
    (hm : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (p^n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    Nat.card (V.map q) = 2 ∧ ∃ t : K.map q, orderOf t = 2 ∧
      (t : H ⧸ ChapterB.minimalParabolicCore T hP) ∈ V.map q := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let D := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : Fact p.Prime := ⟨hp⟩
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hO : pCore 2 (H⧸J) = ⊥ := bot_unique
    ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hSW : (S:Subgroup (H⧸J)) ≤ normalizer (W:Set (H⧸J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hmin).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hVM).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  have hne : W ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff V).mp he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hh)
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  exact corefree_odd_image_involution S hmin D hi.2.2.2 hO ho hp3 hn hcard
    (by simpa only [hcard] using hlarge) e W (map_mono hVT) hSW hWcore hne
end CFSG.Quasithin.ChapterE.Witnesses.OddLinearTwo
