module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers

/-!
# Four-groups in Bender's Sylow normalizer

A two-subgroup of the Sylow normalizer lies in its normal Sylow subgroup.
The already proved ambient four-group centralizer calculation therefore
identifies the centralizer of each four-group in the normalizer with that
particular Sylow subgroup. Conjugating the centralizers shows that an
overlap of two distinct normalizers has order indivisible by four.

The overlap is written using the literal conjugation preimage, so its
orientation is explicit even before the conjugating element is assumed
involutory. This is the first step in the inversion-set argument in
Bender, *Finite groups with large subgroups* (1974), §4, printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

public theorem bender_two_subgroup_le_sylow (V : Subgroup G) (hV : IsPGroup 2 V)
    (hVH : V ≤ normalizer (h.sylow : Set G)) : V ≤ (h.sylow : Subgroup G) := by
  rw [← inf_eq_left] at hVH ⊢
  rwa [hV.inf_normalizer_sylow h.sylow] at hVH

public theorem bender_four_centralizer_eq [IsSimpleGroup G]
    (V : Subgroup G) (hVH : V ≤ normalizer (h.sylow : Set G))
    (hV : Nat.card V = 4) : centralizer (V : Set G) = (h.sylow : Subgroup G) := by
  have hVQ := h.bender_two_subgroup_le_sylow V
    (IsPGroup.of_card (n := 2) (by simpa using hV)) hVH
  let _ := h.sylow_elementaryAbelian
  apply (eq_of_le_of_card_ge
    ((Subgroup.le_centralizer (h.sylow : Subgroup G)).trans (centralizer_le hVQ)) ?_).symm
  rw [h.four_centralizer_card V hV, h.sylow_card]

public theorem bender_mem_normalizer_of_four_overlap [IsSimpleGroup G]
    (u : G) (V : Subgroup G) (hV : Nat.card V = 4)
    (hVH : V ≤ normalizer (h.sylow : Set G))
    (hVuH : V.map (MulAut.conj u).toMonoidHom ≤ normalizer (h.sylow : Set G)) :
    u ∈ normalizer (h.sylow : Set G) := by
  let f := (MulAut.conj u).toMonoidHom
  have hVC := h.bender_four_centralizer_eq V hVH hV
  have hVuc : Nat.card (V.map f) = 4 := by
    rw [card_map_of_injective (MulAut.conj u).injective, hV]
  have hVuC := h.bender_four_centralizer_eq (V.map f) hVuH hVuc
  have hle : (h.sylow : Subgroup G).map f ≤ (h.sylow : Subgroup G) := by
    calc
      _ = (centralizer (V : Set G)).map f := congrArg (Subgroup.map f) hVC.symm
      _ ≤ centralizer (V.map f : Set G) := map_centralizer_le_centralizer_image (V : Set G) f
      _ = _ := hVuC
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj u).injective])

public theorem bender_normalizer_overlap_not_four_dvd [IsSimpleGroup G]
    (u : G) (hu : u ∉ normalizer (h.sylow : Set G)) :
    ¬ 4 ∣ Nat.card (normalizer (h.sylow : Set G) ⊓
      (normalizer (h.sylow : Set G)).comap (MulAut.conj u).toMonoidHom : Subgroup G) := by
  let H := normalizer (h.sylow : Set G)
  let I := H ⊓ H.comap (MulAut.conj u).toMonoidHom
  intro hfour
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := I) 2 (n := 2) hfour
  have hVH : V.map I.subtype ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact v.property.1
  have hVuH : (V.map I.subtype).map (MulAut.conj u).toMonoidHom ≤ H := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact v.property.2
  apply hu (h.bender_mem_normalizer_of_four_overlap u (V.map I.subtype) ?_ hVH hVuH)
  rw [card_map_of_injective I.subtype_injective, hV]
  norm_num

end CFSG.Quasithin.Janko1CentralizerData
