module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Set.Finite.Lemmas
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Maximum-order small movers and their actual kernels

For a finite radical T acting on U with a normal kernel Q, the source
small-mover inequality compares |U:C_U(E)| with |E:E∩Q| and a fixed bound.
There is no elementary-abelian restriction on E. Maximal order forces every
member to contain Q; after this saturation maximality is exactly maximality
of image order. Injective homomorphisms preserve the entire family and join.

These statements supply literal quotient and graph transport for MS93 (5.0),
printed p.912, including replacement radicals smaller than a Sylow subgroup.
-/

@[expose] public section
open Subgroup
namespace Subgroup.SmallMover
variable {G : Type*} [Group G]
def Admissible (U Q T : Subgroup G) (n : ℕ) (E : Subgroup G) : Prop :=
  E ≤ T ∧ (centralizer (E : Set G)).relIndex U ≤ Q.relIndex E ∧
    (centralizer (E : Set G)).relIndex U ≤ n
def Maximal (U Q T : Subgroup G) (n : ℕ) : Set (Subgroup G) :=
  {E | Admissible U Q T n E ∧ ∀ F, Admissible U Q T n F → Nat.card F ≤ Nat.card E}
noncomputable def join (U Q T : Subgroup G) (n : ℕ) : Subgroup G :=
  sSup (Maximal U Q T n)
theorem join_le (U Q T : Subgroup G) (n : ℕ) : join U Q T n ≤ T :=
  sSup_le (fun _ h => h.1.1)
theorem fixed_inf_sup (U Q E : Subgroup G) (hQ : U ≤ centralizer (Q : Set G)) :
    U ⊓ centralizer ((Q ⊔ E : Subgroup G) : Set G) = U ⊓ centralizer (E : Set G) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le (show E ≤ Q ⊔ E from le_sup_right)))
  intro u hu
  refine ⟨hu.1, ?_⟩
  have hQu : Q ≤ centralizer ({u} : Set G) := by
    intro q hq
    simp only [mem_centralizer_singleton_iff]
    exact hQ hu.1 q hq
  have hEu : E ≤ centralizer ({u} : Set G) := by
    intro e he
    simp only [mem_centralizer_singleton_iff]
    exact hu.2 e he
  intro e he
  exact mem_centralizer_singleton_iff.mp ((sup_le hQu hEu) he)
theorem admissible_sup (U Q T E : Subgroup G) [Q.Normal] (n : ℕ)
    (hQT : Q ≤ T) (hQ : U ≤ centralizer (Q : Set G))
    (hE : Admissible U Q T n E) : Admissible U Q T n (Q ⊔ E) := by
  have hfix : (centralizer ((Q ⊔ E : Subgroup G) : Set G)).relIndex U =
      (centralizer (E : Set G)).relIndex U := by
    rw [←inf_relIndex_left, fixed_inf_sup U Q E hQ, inf_relIndex_left]
  exact ⟨sup_le hQT hE.1, by rw [hfix,relIndex_sup_left]; exact hE.2.1,
    by rw [hfix]; exact hE.2.2⟩
theorem maximal_contains_kernel (U Q T : Subgroup G) [Q.Normal] [Finite T]
    (n : ℕ) (hQT : Q ≤ T) (hQ : U ≤ centralizer (Q : Set G))
    {E : Subgroup G} (hE : E ∈ Maximal U Q T n) : Q ≤ E := by
  let : Finite (Q ⊔ E : Subgroup G) := Finite.of_injective
    (inclusion (sup_le hQT hE.1.1)) (inclusion_injective _)
  have heq : E = Q ⊔ E := eq_of_le_of_card_ge le_sup_right
    (hE.2 _ (admissible_sup U Q T E n hQT hQ hE.1))
  exact heq.symm ▸ le_sup_left
theorem maximal_nonempty (U Q T : Subgroup G) [Finite T] (n : ℕ) (hn : 1 ≤ n) :
    (Maximal U Q T n).Nonempty := by
  let : Finite (Subgroup T) := Finite.of_injective (fun A : Subgroup T => (A : Set T)) SetLike.coe_injective
  have hs : {E | Admissible U Q T n E}.Finite :=
    (Set.finite_range (fun A : Subgroup T => A.map T.subtype)).subset (by
      intro E he
      exact ⟨E.subgroupOf T,map_subgroupOf_eq_of_le he.1⟩)
  have hb : Admissible U Q T n ⊥ := by
    have hc : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by ext x; simp [mem_centralizer_iff]
    refine ⟨bot_le, ?_, ?_⟩
    · rw [hc]; simp
    · rw [hc]; simpa using hn
  obtain ⟨E,he,hm⟩ := Set.exists_max_image _ (fun E : Subgroup G => Nat.card E) hs ⟨⊥,hb⟩
  exact ⟨E,he,hm⟩

theorem kernel_le_join (U Q T : Subgroup G) [Q.Normal] [Finite T]
    (n : ℕ) (hn : 1 ≤ n) (hQT : Q ≤ T) (hQ : U ≤ centralizer (Q : Set G)) :
    Q ≤ join U Q T n := by
  obtain ⟨E,hE⟩ := maximal_nonempty U Q T n hn
  exact (maximal_contains_kernel U Q T n hQT hQ hE).trans (le_sSup hE)

variable {H : Type*} [Group H]
theorem centralizer_index_map (i : G →* H) (hi : Function.Injective i)
    (U E : Subgroup G) :
    (centralizer (E.map i : Set H)).relIndex (U.map i) =
      (centralizer (E : Set G)).relIndex U := by
  rw [← inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
    relIndex_map_map_of_injective _ _ hi,inf_relIndex_left]

theorem admissible_map_iff (i : G →* H) (hi : Function.Injective i)
    (U Q T E : Subgroup G) (n : ℕ) :
    Admissible (U.map i) (Q.map i) (T.map i) n (E.map i) ↔ Admissible U Q T n E := by
  unfold Admissible
  rw [map_le_map_iff_of_injective hi,centralizer_index_map i hi,
    relIndex_map_map_of_injective _ _ hi]

theorem maximal_map_iff (i : G →* H) (hi : Function.Injective i)
    (U Q T E : Subgroup G) (n : ℕ) :
    E.map i ∈ Maximal (U.map i) (Q.map i) (T.map i) n ↔ E ∈ Maximal U Q T n := by
  constructor
  · rintro ⟨he,hm⟩
    refine ⟨(admissible_map_iff i hi U Q T E n).mp he,?_⟩
    intro F hF
    have hh := hm (F.map i) ((admissible_map_iff i hi U Q T F n).mpr hF)
    simpa only [card_map_of_injective hi] using hh
  · rintro ⟨he,hm⟩
    refine ⟨(admissible_map_iff i hi U Q T E n).mpr he,?_⟩
    intro F hF
    have hFi : F ≤ i.range := hF.1.trans (map_le_range i T)
    have hFmap : (F.comap i).map i = F := map_comap_eq_self hFi
    have hsm := (admissible_map_iff i hi U Q T (F.comap i) n).mp (hFmap.symm ▸ hF)
    have hh := hm (F.comap i) hsm
    rw [←hFmap,card_map_of_injective hi,card_map_of_injective hi]
    exact hh
theorem join_map (i : G →* H) (hi : Function.Injective i)
    (U Q T : Subgroup G) (n : ℕ) :
    (join U Q T n).map i = join (U.map i) (Q.map i) (T.map i) n := by
  apply le_antisymm
  · rw [join,sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro E
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hE
    exact le_sSup ((maximal_map_iff i hi U Q T E n).mpr hE)
  · apply sSup_le
    intro F hF
    have hr : F ≤ i.range := hF.1.1.trans (map_le_range i T)
    have hm : (F.comap i).map i = F := map_comap_eq_self hr
    have hpre : F.comap i ∈ Maximal U Q T n :=
      (maximal_map_iff i hi U Q T (F.comap i) n).mp (hm.symm ▸ hF)
    rw [←hm]
    exact map_mono (le_sSup hpre)

theorem card_kernel_mul_image (q : G →* H) (E : Subgroup G) (hE : q.ker ≤ E) :
    Nat.card q.ker * Nat.card (E.map q) = Nat.card E := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) q.ker E bot_le hE
  simpa only [relIndex_bot_left,relIndex_ker] using h

theorem maximal_iff_image_maximal (q : G →* H) (U T : Subgroup G) [Finite T]
    (n : ℕ) (hQT : q.ker ≤ T) (hQ : U ≤ centralizer (q.ker : Set G))
    (E : Subgroup G) :
    E ∈ Maximal U q.ker T n ↔ Admissible U q.ker T n E ∧ q.ker ≤ E ∧
      ∀ F, Admissible U q.ker T n F → Nat.card (F.map q) ≤ Nat.card (E.map q) := by
  let : Finite q.ker := Finite.of_injective (inclusion hQT) (inclusion_injective _)
  constructor
  · intro hE
    have hk := maximal_contains_kernel U q.ker T n hQT hQ hE
    refine ⟨hE.1,hk,?_⟩
    intro F hF
    have hm := hE.2 _ (admissible_sup U q.ker T F n hQT hQ hF)
    rw [←card_kernel_mul_image q _ le_sup_left,←card_kernel_mul_image q E hk] at hm
    have he : (q.ker ⊔ F).map q = F.map q := by
      simp only [Subgroup.map_sup,Subgroup.map_ker_self,bot_sup_eq]
    rw [he] at hm
    exact (Nat.le_of_mul_le_mul_left hm Nat.card_pos)
  · rintro ⟨hE,hk,hm⟩
    refine ⟨hE,?_⟩
    intro F hF
    let : Finite (q.ker ⊔ F : Subgroup G) := Finite.of_injective
      (inclusion (sup_le hQT hF.1)) (inclusion_injective _)
    have he : (q.ker ⊔ F).map q = F.map q := by
      simp only [Subgroup.map_sup,Subgroup.map_ker_self,bot_sup_eq]
    calc
      Nat.card F ≤ Nat.card (q.ker ⊔ F : Subgroup G) :=
        Nat.card_le_card_of_injective (inclusion le_sup_right) (inclusion_injective _)
      _ = Nat.card q.ker * Nat.card (F.map q) := by
        rw [←card_kernel_mul_image q _ le_sup_left,he]
      _ ≤ Nat.card q.ker * Nat.card (E.map q) := Nat.mul_le_mul_left _ (hm F hF)
      _ = Nat.card E := card_kernel_mul_image q E hk
end Subgroup.SmallMover
