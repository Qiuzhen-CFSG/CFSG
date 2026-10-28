module

public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Local Sylow control through a characteristic subgroup

A characteristic subgroup of a p-subgroup `Q` can trap `N_G(Q)` inside
a local subgroup `M`. If `Q` is Sylow in `M ∩ C`, the normalizer-index
criterion then makes `Q` Sylow in `C`. For `Q = C_T(v)` proper in a
Sylow subgroup `T`, this excludes fusion of `v` with any element
centralized by all of `T`, by comparing Sylow orders in the centralizers.

This packages the finite-group argument in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
Lemma 13.2.6, printed p.879. There `Q = C_T(v)` and the characteristic
subgroup is `Baum(Q) = Baum(T)`. The local module calculation and the
normalizer bound remain inputs; no quasithin classification is assumed.
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A characteristic subgroup with local normalizer promotes the local
Sylow index to the full overgroup. -/
public theorem not_dvd_relIndex_of_characteristic_normalizer
    (Q M C : Subgroup G) (B : Subgroup Q) [B.Characteristic]
    (hQ : IsPGroup p Q) (hQC : Q ≤ C)
    (hlocal : ¬ p ∣ Q.relIndex (M ⊓ C))
    (hB : normalizer (B.map Q.subtype : Set G) ≤ M) :
    ¬ p ∣ Q.relIndex C := by
  apply not_dvd_relIndex_of_normalizer_inf_le Q (M ⊓ C) C hQ hQC hlocal
  exact le_inf (inf_le_left.trans
    ((normalizer_le_normalizer_characteristic_image Q B).trans hB)) inf_le_right

/-- The promoted Sylow subgroup has exactly the specified ambient image. -/
public theorem exists_sylow_of_characteristic_normalizer
    (Q M C : Subgroup G) (B : Subgroup Q) [B.Characteristic]
    (hQ : IsPGroup p Q) (hQC : Q ≤ C)
    (hlocal : ¬ p ∣ Q.relIndex (M ⊓ C))
    (hB : normalizer (B.map Q.subtype : Set G) ≤ M) :
    ∃ P : Sylow p C, (P : Subgroup C).map C.subtype = Q := by
  have hindex := not_dvd_relIndex_of_characteristic_normalizer Q M C B hQ hQC
    hlocal hB
  let P : Sylow p C := (hQ.comap_subtype (K := C)).toSylow hindex
  exact ⟨P, map_subgroupOf_eq_of_le hQC⟩

end Subgroup

namespace Sylow

open Subgroup

/-- If a proper Sylow centralizer has a characteristic subgroup whose
normalizer stays local, local Sylow maximality excludes fusion with an
element centralized by the whole Sylow subgroup. -/
public theorem not_isConj_of_characteristic_centralizer_normalizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (M : Subgroup G) (v z : G)
    (B : Subgroup ↥((T : Subgroup G) ⊓ centralizer ({v} : Set G)))
    [B.Characteristic]
    (hlocal : ¬ p ∣ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex
      (M ⊓ centralizer ({v} : Set G)))
    (hB : normalizer (B.map
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).subtype : Set G) ≤ M)
    (hproper : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≠ (T : Subgroup G))
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) : ¬ IsConj v z := by
  have hindex := not_dvd_relIndex_of_characteristic_normalizer
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) M
    (centralizer ({v} : Set G)) B (T.isPGroup'.to_le inf_le_left) inf_le_right
    hlocal hB
  apply not_isConj_of_sylow_centralizer_card_lt v z
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) (T : Subgroup G)
    (T.isPGroup'.to_le inf_le_left) T.isPGroup' inf_le_right hz hindex
  exact lt_of_le_of_ne (card_le_of_le inf_le_left) (fun h =>
    hproper (eq_of_le_of_card_ge inf_le_left h.ge))

end Sylow
