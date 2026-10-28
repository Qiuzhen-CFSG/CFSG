module

public import CFSG.Quasithin.Chapter6.SourceDefs
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Action

/-!
# Irreducibility of the natural modules in the escape argument

SL₂ is transitive on nonzero vectors, so an invariant additive subgroup of
its natural module is zero or the whole module. Transporting this fact through
`Source.IsNaturalModule` gives the assertion for `V_L`. For `R/E` we retain
both actual relative quotients and an equation intertwining ambient conjugation.
Every intermediate subgroup is normalized by `R`, since its image in the
additive quotient is normal. Thus `L₁ = L₀ ∨ R` transfers invariance under `L₀`
to invariance under `L₁`, and transitivity finishes the proof.

`IsNaturalSectionFour` is the conditional natural-module input of 6.1.25(3),
including the field order from 6.1.25(1). Its existence and the geometric
supplement equality belong to the source-theorem assembly. No irreducibility
is included in that input. The results concern all subgroups, without an
assumption of linearity over the field of four elements.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas 6.1.21,
6.1.25(3), and the proof of 6.1.26, printed pp.675–679.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G]

/-- Invariant additive subgroups of the genuine natural module are trivial or full. -/
lemma IsNaturalModule.invariant_subgroup {L V : Subgroup G} {n : ℕ}
    (h : IsNaturalModule L V n) (A : Subgroup G) (hAV : A ≤ V)
    (hLA : L ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = V := by
  obtain ⟨F, hF, hfin, hchar, hcard, e, f, hf⟩ := h
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  apply le_antisymm hAV
  obtain ⟨x, hxA, hx⟩ := SetLike.not_le_iff_exists.mp (mt le_bot_iff.mp hA)
  simp only [Subgroup.mem_bot] at hx
  let v : V := ⟨x, hAV hxA⟩
  have hv : Multiplicative.toAdd (f v) ≠ 0 := by
    intro hv
    have : v = 1 := f.injective (hv.trans f.map_one.symm)
    exact hx (congrArg Subtype.val this)
  intro y hy
  by_cases hy1 : y = 1
  · subst y; exact A.one_mem
  let w : V := ⟨y, hy⟩
  have hw : Multiplicative.toAdd (f w) ≠ 0 := by
    intro hw
    have : w = 1 := f.injective (hw.trans f.map_one.symm)
    exact hy1 (congrArg Subtype.val this)
  obtain ⟨s, hs⟩ := Theory.SpecificGroups.SymplecticFour.natural_transitive hv hw
  obtain ⟨q, hq⟩ := e.surjective s
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have he : e (QuotientGroup.mk' (pCore 2 L) l) = s := by rw [hl, hq]
  have hc := hf l v
  rw [he] at hc
  change ((f.symm (Multiplicative.ofAdd (Matrix.mulVec s.val
    (Multiplicative.toAdd (f v))))) : G) = _ at hc
  rw [hs] at hc
  change ((f.symm (f w)) : G) = _ at hc
  rw [f.symm_apply_apply] at hc
  change (w : G) ∈ A
  rw [hc]
  exact (mem_normalizer_iff.mp (hLA l.property) x).mp hxA

/-- A supplement to a subgroup centralizing the module has the same invariant subgroups. -/
lemma IsNaturalModule.invariant_subgroup_of_supplement {L V D R : Subgroup G} {n : ℕ}
    (h : IsNaturalModule L V n) (hL : L ≤ D ⊔ R)
    (hR : R ≤ centralizer (V : Set G))
    (A : Subgroup G) (hAV : A ≤ V) (hDA : D ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = V := by
  apply h.invariant_subgroup A hAV
  apply hL.trans
  apply sup_le hDA
  apply le_trans _ (centralizer_le_normalizer _)
  intro r hr
  exact mem_centralizer_iff.mpr fun a ha => mem_centralizer_iff.mp (hR hr) a (hAV ha)

end CFSG.Quasithin.Chapter6.Source

open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.Escape
variable {G : Type*} [Group G]

/-- An equivariant model of the action of `J/R` on `R/E`. Normality is
relative to the displayed overgroups; equivariance also forces `E` normal in `J`. -/
structure NaturalSectionModel (J R E : Subgroup G) (F : Type*) [Field F] where
  R_le : R ≤ J
  E_le : E ≤ R
  R_normal : (R.subgroupOf J).Normal
  E_normal : (E.subgroupOf R).Normal
  actor : letI := R_normal; (J ⧸ R.subgroupOf J) ≃* Matrix.SpecialLinearGroup (Fin 2) F
  vectors : letI := E_normal; (R ⧸ E.subgroupOf R) ≃* Multiplicative (Fin 2 → F)
  intertwining : ∀ (j : J) (r : R),
    letI := R_normal
    letI := E_normal
    vectors (QuotientGroup.mk' (E.subgroupOf R)
      ⟨(j : G) * (r : G) * (j : G)⁻¹,
        (mem_normalizer_iff.mp
          ((normal_subgroupOf_iff_le_normalizer R_le).mp R_normal j.property) r).mp
            r.property⟩) =
      Multiplicative.ofAdd (Representation.specialLinearNatural 2
        (actor (QuotientGroup.mk' (R.subgroupOf J) j))
        (Multiplicative.toAdd (vectors (QuotientGroup.mk' (E.subgroupOf R) r))))

namespace NaturalSectionModel
variable {J R E D : Subgroup G} {F : Type*} [Field F]
variable (m : NaturalSectionModel J R E F)
include m

/-- Quotient coordinates, retaining the kernel `E` inside `R`. -/
def coordinates : R →* Multiplicative (Fin 2 → F) := by
  let := m.E_normal
  exact m.vectors.toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf R))

lemma coordinates_eq_one (r : R) : m.coordinates r = 1 ↔ (r : G) ∈ E := by
  let := m.E_normal
  change m.vectors (QuotientGroup.mk' (E.subgroupOf R) r) = 1 ↔ _
  rw [← m.vectors.map_one, m.vectors.injective.eq_iff]
  exact QuotientGroup.eq_one_iff r

lemma E_normal_in_actor : (E.subgroupOf J).Normal := by
  let := m.E_normal
  let := m.R_normal
  constructor
  intro e he j
  let r : R := ⟨(e : G), m.E_le he⟩
  have hr : m.vectors (QuotientGroup.mk' (E.subgroupOf R) r) = 1 :=
    (m.coordinates_eq_one r).mpr he
  have hc := m.intertwining j r
  rw [hr] at hc
  simp only [show Multiplicative.toAdd (1 : Multiplicative (Fin 2 → F)) = 0 from rfl,
    map_zero] at hc
  exact (m.coordinates_eq_one _).mp hc

/-- Irreducibility on the actual subgroup interval, with no scalar-closure assumption. -/
lemma invariant_interval (hJ : J = D ⊔ R) (A : Subgroup G)
    (hEA : E ≤ A) (hAR : A ≤ R) (hDA : D ≤ normalizer (A : Set G)) :
    A = E ∨ A = R := by
  let := m.E_normal
  let := m.R_normal
  let K := A.subgroupOf R
  have hker : m.coordinates.ker ≤ K := by
    intro r hr
    exact hEA ((m.coordinates_eq_one r).mp hr)
  have hcomap : (K.map m.coordinates).comap m.coordinates = K :=
    Subgroup.comap_map_eq_self hker
  have hKn : K.Normal := hcomap ▸ inferInstance
  have hRA : R ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAR).mp hKn
  have hJA : J ≤ normalizer (A : Set G) := by rw [hJ]; exact sup_le hDA hRA
  by_cases hAE : A ≤ E
  · exact Or.inl (le_antisymm hAE hEA)
  right
  obtain ⟨x, hxA, hxE⟩ := SetLike.not_le_iff_exists.mp hAE
  let v : R := ⟨x, hAR hxA⟩
  have hv : Multiplicative.toAdd (m.coordinates v) ≠ 0 := by
    intro hv
    exact hxE ((m.coordinates_eq_one v).mp hv)
  have hmap : K.map m.coordinates = ⊤ := by
    apply top_unique
    intro w _
    by_cases hw : w = 1
    · subst w; exact (K.map m.coordinates).one_mem
    obtain ⟨s, hs⟩ := Theory.SpecificGroups.SymplecticFour.natural_transitive hv hw
    obtain ⟨q, hq⟩ := m.actor.surjective s
    obtain ⟨j, hj⟩ := QuotientGroup.mk'_surjective (R.subgroupOf J) q
    have he : m.actor (QuotientGroup.mk' (R.subgroupOf J) j) = s := by rw [hj, hq]
    let v' : R := ⟨(j : G) * x * (j : G)⁻¹,
      (mem_normalizer_iff.mp
        ((normal_subgroupOf_iff_le_normalizer m.R_le).mp m.R_normal j.property) x).mp
          (hAR hxA)⟩
    refine ⟨v', (mem_normalizer_iff.mp (hJA j.property) x).mp hxA, ?_⟩
    have hc := m.intertwining j v
    rw [he] at hc
    exact hc.trans (congrArg Multiplicative.ofAdd hs)
  rw [hmap, Subgroup.comap_top] at hcomap
  exact le_antisymm hAR (Subgroup.subgroupOf_eq_top.mp hcomap.symm)
end NaturalSectionModel

/-- The genuine natural section over a field of order four, as supplied by
6.1.25. Both the acting group and the module are identified equivariantly. -/
def IsNaturalSectionFour (J R E : Subgroup G) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
    Nat.card k = 4 ∧ Nonempty (NaturalSectionModel J R E k)

/-- The source model yields irreducibility for any supplement of `R`. -/
theorem IsNaturalSectionFour.invariant_interval {J R E D : Subgroup G}
    (h : IsNaturalSectionFour J R E) (hJ : J = D ⊔ R) :
    ∀ A : Subgroup G, E ≤ A → A ≤ R →
      D ≤ normalizer (A : Set G) → A = E ∨ A = R := by
  obtain ⟨k, hk, hfin, hchar, hcard, ⟨m⟩⟩ := h
  exact m.invariant_interval hJ

/-- The `R/E` irreducibility premise consumed by the terminal size argument. -/
theorem section_irreducible_of_natural {T L V : Subgroup G} {g l : G}
    (hmodel : IsNaturalSectionFour (L1 T L V l) (R T L V l) (E T L V l))
    (hsupplement : L1 T L V l = L0 L V g l ⊔ R T L V l) :
    ∀ A : Subgroup G, E T L V l ≤ A → A ≤ R T L V l →
      L0 L V g l ≤ normalizer (A : Set G) →
        A = E T L V l ∨ A = R T L V l :=
  hmodel.invariant_interval hsupplement

/-- The genuine normalized action on `V_L`, together with its irreducibility.
The normalization premise is retained explicitly: containment of `L` in
`L₀R` by itself does not assert that `L₀` acts on `V_L`. -/
theorem layer_irreducible_of_natural {T L V : Subgroup G} {g l : G}
    (hmodel : IsNaturalModule L (layer L V) 2)
    (hL : L ≤ L0 L V g l ⊔ R T L V l)
    (hR : R T L V l ≤ centralizer (layer L V : Set G))
    (hD : L0 L V g l ≤ normalizer (layer L V : Set G)) :
    L0 L V g l ≤ normalizer (layer L V : Set G) ∧
      ∀ A : Subgroup G, A ≤ layer L V →
        L0 L V g l ≤ normalizer (A : Set G) → A = ⊥ ∨ A = layer L V :=
  ⟨hD, hmodel.invariant_subgroup_of_supplement hL hR⟩

end CFSG.Quasithin.Chapter6.Source.Escape
