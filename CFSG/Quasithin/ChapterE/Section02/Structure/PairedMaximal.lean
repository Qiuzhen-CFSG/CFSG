module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentAutomizer

/-!
# The product of the two component intersections with the original maximal

The normalizer in a simple component of its nontrivial proper maximal
intersection is a proper Sylow-stabilizer invariant seed. Minimal
parabolicity places that normalizer back in the intersection, proving
self-normalization. In a commuting component pair, an element of M then
has both component coordinates in M. This gives the exact product with T,
without requiring a particular model or Borel calculation.

Source: Aschbacher–Smith E.2.2(1), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

/-- The original maximal intersection is self-normalizing inside its simple component. -/
theorem component_maximal_intersection_self_normalizing
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    K ⊓ normalizer ((K ⊓ ChapterB.minimalParabolicMax T hP : Subgroup H) : Set H) =
      K ⊓ ChapterB.minimalParabolicMax T hP := by
  let M := ChapterB.minimalParabolicMax T hP
  let A := K ⊓ M
  let R := K ⊓ normalizer (A : Set H)
  have ho := generating_component_orbit_eq_residual hH T hK hgen
  let := hK.2
  have heven : 2 ∣ Nat.card K := by
    by_contra hn
    have hodd : Odd (Nat.card K) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hn)
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)
  obtain ⟨hAb,hAK⟩ := ChapterB.component_maximal_intersection T hP hK heven ho
  have hAR : A ≤ R := le_inf inf_le_left A.le_normalizer
  have hRb : R ≠ ⊥ := fun he => hAb (bot_unique (hAR.trans he.le))
  have hRK : R ≠ K := by
    intro he
    have hn : K ≤ normalizer (A : Set H) := he ▸ inf_le_right
    let : (A.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf K) inferInstance with hb | ht
    · apply hAb
      have hh := congrArg (map K.subtype) hb
      simpa only [map_subgroupOf_eq_of_le (show A ≤ K from inf_le_left),Subgroup.map_bot] using hh
    · apply hAK
      have hh := congrArg (map K.subtype) ht
      simpa only [map_subgroupOf_eq_of_le (show A ≤ K from inf_le_left),
        ← MonoidHom.range_eq_map,range_subtype] using hh
  have hSA : (T : Subgroup H) ⊓ normalizer (K : Set H) ≤ normalizer (A : Set H) := by
    apply (le_inf inf_le_right ?_).trans inf_normalizer_le_normalizer_inf
    exact inf_le_left.trans ((ChapterB.minimalParabolicMax_spec T hP).2.trans M.le_normalizer)
  have hSR : (T : Subgroup H) ⊓ normalizer (K : Set H) ≤ normalizer (R : Set H) :=
    (le_inf inf_le_right (hSA.trans (normalizer (A : Set H)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hRM : R ≤ M := ChapterB.component_seed_le_minimalParabolicMax T hP hK
    inf_le_left hRb hRK hSR
  exact le_antisymm (le_inf inf_le_left hRM) hAR

/-- The full maximal product formula for the same exchanged simple component. -/
theorem source_paired_maximal_product
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    ∃ t : T, K.map (MulAut.conj (t:H)).toMonoidHom ≠ K ∧
      (ChapterB.minimalParabolicMax T hP : Set H) =
        (ChapterB.minimalParabolicMax T hP ⊓ K : Subgroup H) *
          (((ChapterB.minimalParabolicMax T hP ⊓ K).map
            (MulAut.conj (t:H)).toMonoidHom : Subgroup H) : Set H) * (T : Set H) := by
  let M := ChapterB.minimalParabolicMax T hP
  rcases component_normal_or_pair hH T hK hgen with h | ⟨t,hne,hD,hcomm,hR,hres,hswap,_⟩
  · exact (hn h.1).elim
  let D := K.map (MulAut.conj (t:H)).toMonoidHom
  let := hR
  have hTM : (T : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec T hP).2
  have hAD : (M ⊓ K).map (MulAut.conj (t:H)).toMonoidHom = M ⊓ D := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (t:H)).injective]
    have hm : M.map (MulAut.conj (t:H)).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hTM t.property))
    rw [hm]
  have hself := component_maximal_intersection_self_normalizing hH T hP hK hgen
  have hDK : D ≤ centralizer (K : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm];exact hcomm)
  have hjoin : (K ⊔ D) ⊔ (T : Subgroup H) = ⊤ := by
    rw [← hres]
    exact pResidual_sup_sylow_eq_top T
  refine ⟨t,hne,?_⟩
  rw [hAD]
  ext x
  constructor
  · intro hx
    have hxg : x ∈ (K ⊔ D) ⊔ (T : Subgroup H) := hjoin ▸ mem_top x
    obtain ⟨r,hr,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hxg
    have hrM : r ∈ M := by
      simpa only [mul_inv_cancel_right] using M.mul_mem hx (M.inv_mem (hTM hs))
    have hrprod : r ∈ (K : Set H) * (D : Set H) := by
      rw [← coe_mul_of_right_le_normalizer_left K D (hDK.trans (Subgroup.centralizer_le_normalizer _))]
      exact hr
    obtain ⟨k,hk,d,hd,hkd⟩ := hrprod
    have hdA : d ∈ normalizer ((K ⊓ M : Subgroup H) : Set H) :=
      (Subgroup.centralizer_le_normalizer _) (fun a ha => hDK hd a ha.1)
    have hrA : r ∈ normalizer ((K ⊓ M : Subgroup H) : Set H) := by
      apply inf_normalizer_le_normalizer_inf
      refine ⟨?_,M.le_normalizer hrM⟩
      rw [←hkd]
      exact (normalizer (K : Set H)).mul_mem (K.le_normalizer hk)
        (Subgroup.centralizer_le_normalizer _ (hDK hd))
    have hkA : k ∈ normalizer ((K ⊓ M : Subgroup H) : Set H) := by
      have hh := (normalizer ((K ⊓ M : Subgroup H) : Set H)).mul_mem hrA
        ((normalizer ((K ⊓ M : Subgroup H) : Set H)).inv_mem hdA)
      simpa only [←hkd,mul_inv_cancel_right] using hh
    have hkM : k ∈ M := (show k ∈ K ⊓ M from hself ▸ ⟨hk,hkA⟩).2
    have hdM : d ∈ M := by
      have hh := M.mul_mem (M.inv_mem hkM) hrM
      simpa only [←hkd,inv_mul_cancel_left] using hh
    exact Set.mem_mul.mpr ⟨r,Set.mem_mul.mpr ⟨k,⟨hkM,hk⟩,d,⟨hdM,hd⟩,hkd⟩,s,hs,rfl⟩
  · rintro ⟨r,⟨k,hk,d,hd,rfl⟩,s,hs,rfl⟩
    exact M.mul_mem (M.mul_mem hk.1 hd.1) (hTM hs)
end CFSG.Quasithin.ChapterE.Structure
