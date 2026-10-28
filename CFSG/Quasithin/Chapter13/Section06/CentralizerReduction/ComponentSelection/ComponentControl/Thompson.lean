module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import Theory.GroupTheory.ElementaryThompsonComponent

/-!
# The Frattini–Thompson step of 13.6.16

Assertion (2), applied to the nontrivial characteristic elementary Thompson
subgroup of T_v, implies K₀ = [K₀,J(T_v)]. The intrinsic Thompson subgroup
of T_v and that of its actual Sylow realization in K₀T_v both map to the
literal ambient subgroup `elementaryAbelianMaxJ (Tv T v)`.

Tv-invariance makes K₀ normal in K₀T_v. The general C-component dichotomy
and Frattini argument are applied in that overgroup, with the radical of
K₀ transported through its actual subgroup equivalence. In the radical
branch, J(T_v) O∞(K₀) is normal in K₀T_v; Frattini and intersection with K₀
contradict assertion (2). There is no inference that J(T_v) ≤ O∞(K₀).

The final theorem is the independent implication (2) → (3). Its assembly
owner must prove assertion (2) from the earlier source setup. The index-two
and movement hypotheses are retained, although this final implication no
longer needs them after assertion (2) has been supplied.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final paragraph
of Lemma 13.6.16, printed p.930 / PDF p.947.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G]

/-- Characteristicity is inside the actual centralizer T_v. -/
theorem thompson_centralizer_characteristic (T : Subgroup G) (v : G) :
    (elementaryAbelianMaxJ (⊤ : Subgroup (Tv T v))).Characteristic :=
  elementaryAbelianMaxJ_top_characteristic

/-- The intrinsic elementary Thompson subgroup of T_v maps to its
 literal ambient elementary Thompson subgroup. -/
theorem thompson_centralizer_map (T : Subgroup G) (v : G) :
    (elementaryAbelianMaxJ (⊤ : Subgroup (Tv T v))).map (Tv T v).subtype =
      elementaryAbelianMaxJ (Tv T v) := by
  rw [← elementaryAbelianMaxJ_map_injective (Tv T v).subtype (Tv T v).subtype_injective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- Transport from an actual Sylow realization in K₀T_v to G. -/
theorem thompson_join_sylow_map (T K : Subgroup G) (v : G)
    (S : Sylow 2 ↥(K ⊔ Tv T v))
    (hS : (S : Subgroup ↥(K ⊔ Tv T v)).map (K ⊔ Tv T v).subtype = Tv T v) :
    (elementaryAbelianMaxJ (S : Subgroup ↥(K ⊔ Tv T v))).map (K ⊔ Tv T v).subtype =
      elementaryAbelianMaxJ (Tv T v) := by
  rw [← elementaryAbelianMaxJ_map_injective _ (K ⊔ Tv T v).subtype_injective, hS]

variable [Finite G]

/-- The nonidentity element v lies in T_v, so this finite two-group and
 its elementary Thompson subgroup are nontrivial. -/
theorem thompson_centralizer_ne_bot (T : Sylow 2 G) (v : G)
    (hvT : v ∈ T) (hv : v ≠ 1) :
    elementaryAbelianMaxJ (⊤ : Subgroup (Tv (T : Subgroup G) v)) ≠ ⊥ := by
  have hR : Tv (T : Subgroup G) v ≠ ⊥ := by
    intro he
    exact hv (mem_bot.mp (he ▸
      (show v ∈ Tv (T : Subgroup G) v from
        ⟨hvT, mem_centralizer_singleton_iff.mpr rfl⟩)))
  let : Nontrivial (Tv (T : Subgroup G) v) := (nontrivial_iff_ne_bot _).mpr hR
  exact elementaryAbelianMaxJ_top_ne_bot_of_isPGroup (T.isPGroup'.to_le inf_le_left)

/-- Assertion (2) of 13.6.16 implies assertion (3), with the genuine local
 family, relative normality, Sylow witnesses, and ambient Thompson subgroup.
 The parent component-control task retains discharge of `hcontrol`. -/
theorem eq_commutator_thompson_of_characteristic_normalizers
    (T : Sylow 2 G) (z v : G) (hvT : v ∈ T) (hv : v ≠ 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (_hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (K₀ : Subgroup G)
    (hK₀ : K₀ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hR : Tv (T : Subgroup G) v ≤ normalizer (K₀ : Set G))
    (_hmoving : ¬ K₀ ≤ centralizer ({z} : Set G))
    (hcontrol : ∀ C : Subgroup (Tv (T : Subgroup G) v), C.Characteristic → C ≠ ⊥ →
      (solvableRadical K₀).map K₀.subtype ⊔
        (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) < K₀) :
    K₀ = ⁅K₀, elementaryAbelianMaxJ (Tv (T : Subgroup G) v)⁆ := by
  let R := Tv (T : Subgroup G) v
  let H := K₀ ⊔ R
  let B := K₀.subgroupOf H
  obtain ⟨S, hS⟩ := hSylow.restrict (show R ≤ H from le_sup_right)
    (show H ≤ Gv v from sup_le hK₀.1 inf_le_right)
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K₀.le_normalizer hR)
  have hB : B.IsCComponent := hK₀.2.1
  have hBmap : B.map H.subtype = K₀ := map_subgroupOf_eq_of_le le_sup_left
  have hgen : B ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, hBmap, hS, ← MonoidHom.range_eq_map, range_subtype]
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ R := thompson_join_sylow_map (T : Subgroup G) K₀ v S hS
  have hrad : ((solvableRadical B).map B.subtype).map H.subtype =
      (solvableRadical K₀).map K₀.subtype := by
    have he := congrArg (map K₀.subtype)
      (map_solvableRadical_equiv (subgroupOfEquivOfLe (show K₀ ≤ H from le_sup_left)))
    rw [map_map] at he ⊢
    convert he using 1
    congr 1
  have hstrict : (solvableRadical K₀).map K₀.subtype ⊔
      (K₀ ⊓ normalizer (elementaryAbelianMaxJ R : Set G)) < K₀ := by
    have hh := hcontrol (elementaryAbelianMaxJ (⊤ : Subgroup R))
      (thompson_centralizer_characteristic (T : Subgroup G) v)
      (thompson_centralizer_ne_bot T v hvT hv)
    rwa [thompson_centralizer_map] at hh
  have hn : (normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)).map H.subtype ≤
      normalizer (elementaryAbelianMaxJ R : Set G) := by
    rw [← hJmap]
    exact (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
  have hstrictB : (solvableRadical B).map B.subtype ⊔
      (B ⊓ normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)) < B := by
    apply (map_lt_map_iff_of_injective H.subtype_injective).mp
    rw [Subgroup.map_sup, hrad, hBmap]
    apply lt_of_le_of_lt (sup_le_sup_left ?_ _) hstrict
    exact le_inf (by rw [← hBmap]; exact map_mono inf_le_left)
      ((map_mono inf_le_right).trans hn)
  have he := congrArg (map H.subtype)
    (eq_commutator_maxJ_of_radical_normalizer_lt S B hB hgen hstrictB)
  rwa [map_commutator, hBmap, hJmap] at he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
