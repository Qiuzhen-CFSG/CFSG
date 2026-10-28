module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.GroupTheory.PCoreSurjective

/-!
# Lifting the parabolics of the actual star quotient

A subgroup of `Source.Hstar H` has a canonical full preimage inside H.
The map onto the chosen subgroup has kernel the ambient image of O₂(H),
restricted to that preimage. Since this is a two-group, its intrinsic
two-core quotient is isomorphic to the chosen subgroup's intrinsic
two-core quotient. The equivalence retains quotient representatives.

A strict enlargement of the marked intersection H ∩ M lifts to a member
of `Source.Hz`; the nontrivial two-core clause is inherited from H. A
solvable preimage is placed in M by the explicit uniform earlier result
13.8.13. These facts supply the lifting steps in Aschbacher–Smith 13.8.25,
combined manuscript of 1 March 2004, printed pp.959–960 (PDF pp.976–977).
Only relative normality is used. The parabolic quotient models and the
source identifications must still be supplied by final assembly.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
variable {G : Type*} [Group G]

/-- The full preimage in H of a subgroup of the literal star quotient. -/
def liftStar (H : Subgroup G) (P : Subgroup (Source.Hstar H)) : Subgroup G :=
  (P.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

theorem liftStar_le (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    liftStar H P ≤ H := map_subtype_le _

theorem liftStar_subgroupOf (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    (liftStar H P).subgroupOf H = P.comap (QuotientGroup.mk' (pCore 2 H)) :=
  comap_map_eq_self_of_injective H.subtype_injective _

theorem starImage_liftStar (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    Source.starImage H (liftStar H P) = P := by
  rw [Source.starImage, liftStar_subgroupOf]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

/-- The full preimage adds precisely the quotient kernel. -/
theorem liftStar_starImage (H X : Subgroup G) (hXH : X ≤ H) :
    liftStar H (Source.starImage H X) = X ⊔ Source.QH H := by
  rw [liftStar, Source.starImage, comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_eq_of_le hXH]
  rfl

theorem liftStar_starImage_of_core_le (H X : Subgroup G) (hXH : X ≤ H)
    (hcore : Source.QH H ≤ X) : liftStar H (Source.starImage H X) = X := by
  rw [liftStar_starImage H X hXH, sup_eq_left.mpr hcore]

theorem liftStar_le_iff (H : Subgroup G) (P Q : Subgroup (Source.Hstar H)) :
    liftStar H P ≤ liftStar H Q ↔ P ≤ Q := by
  constructor
  · intro h
    have hm := map_mono (f := QuotientGroup.mk' (pCore 2 H))
      (comap_mono (f := H.subtype) h)
    change Source.starImage H (liftStar H P) ≤ Source.starImage H (liftStar H Q) at hm
    simpa only [starImage_liftStar] using hm
  · intro h
    exact map_mono (comap_mono h)

theorem liftStar_lt_iff (H : Subgroup G) (P Q : Subgroup (Source.Hstar H)) :
    liftStar H P < liftStar H Q ↔ P < Q := by
  simp only [lt_iff_le_not_ge, liftStar_le_iff]

theorem le_liftStar_iff (H X : Subgroup G) (hXH : X ≤ H)
    (P : Subgroup (Source.Hstar H)) :
    X ≤ liftStar H P ↔ Source.starImage H X ≤ P := by
  constructor
  · intro h
    have hm := map_mono (f := QuotientGroup.mk' (pCore 2 H))
      (comap_mono (f := H.subtype) h)
    change Source.starImage H X ≤ Source.starImage H (liftStar H P) at hm
    simpa only [starImage_liftStar] using hm
  · intro h x hx
    exact mem_map.mpr ⟨⟨x, hXH hx⟩,
      h (mem_map.mpr ⟨⟨x, hXH hx⟩, hx, rfl⟩), rfl⟩

theorem twoCore_le_liftStar (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    Source.QH H ≤ liftStar H P := by
  apply map_mono
  intro x hx
  change QuotientGroup.mk' (pCore 2 H) x ∈ P
  have he : QuotientGroup.mk' (pCore 2 H) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [he]
  exact P.one_mem

/-- A strict enlargement of the marked intersection gives an actual new
member of Hz. Its nontrivial two-core is inherited from O₂(H). -/
theorem liftStar_mem_Hz (L₁ T G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (P Q : Subgroup (Source.Hstar H))
    (hbase : Source.starImage H (L₁ ⊔ T) ≤ Q)
    (hinter : liftStar H P = H ⊓ M) (hPQ : P < Q) :
    liftStar H Q ∈ Source.Hz L₁ T G₁ M := by
  have hbase' := (le_liftStar_iff H (L₁ ⊔ T) hH.1.2 Q).mpr hbase
  have hn : H ≤ normalizer (Source.QH H : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 H)).mp
    have he : (Source.QH H).subgroupOf H = pCore 2 H :=
      comap_map_eq_self_of_injective H.subtype_injective _
    change ((Source.QH H).subgroupOf H).Normal
    rw [he]
    infer_instance
  refine ⟨⟨?_, hbase'⟩, (liftStar_le H Q).trans hH.2.1, ?_⟩
  · change (liftStar H Q).pCoreIn 2 ≠ ⊥
    intro he
    have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      (twoCore_le_liftStar H Q) ((liftStar_le H Q).trans hn)
    have hzero : Source.QH H = ⊥ := le_bot_iff.mp (hc.trans he.le)
    exact hH.1.1 hzero
  · intro hQM
    have hQP : liftStar H Q ≤ liftStar H P := by
      rw [hinter]
      exact le_inf (liftStar_le H Q) hQM
    exact hPQ.not_ge ((liftStar_le_iff H Q P).mp hQP)

/-- The natural map from the full preimage onto the chosen quotient subgroup. -/
def liftStarMap (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    liftStar H P →* P where
  toFun x := ⟨QuotientGroup.mk' (pCore 2 H) ⟨x, liftStar_le H P x.property⟩, by
    obtain ⟨y, hy, he⟩ := x.property
    have he' : y = ⟨x, liftStar_le H P x.property⟩ := Subtype.ext he
    exact he' ▸ hy⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := by
    apply Subtype.ext
    exact (QuotientGroup.mk' (pCore 2 H)).map_mul
      ⟨x, liftStar_le H P x.property⟩ ⟨y, liftStar_le H P y.property⟩

theorem liftStarMap_surjective (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    Function.Surjective (liftStarMap H P) := by
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x.val
  refine ⟨⟨y, mem_map.mpr ⟨y, ?_, rfl⟩⟩, ?_⟩
  · change QuotientGroup.mk' (pCore 2 H) y ∈ P
    rw [hy]
    exact x.property
  · exact Subtype.ext hy

theorem liftStarMap_kernel (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    (liftStarMap H P).ker = (Source.QH H).subgroupOf (liftStar H P) := by
  ext x
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change (QuotientGroup.mk' (pCore 2 H) ⟨x, liftStar_le H P x.property⟩ = 1) ↔
    (x : G) ∈ (pCore 2 H).map H.subtype
  rw [show (QuotientGroup.mk' (pCore 2 H)
      ⟨x, liftStar_le H P x.property⟩ = 1) ↔
      (⟨x, liftStar_le H P x.property⟩ : H) ∈ pCore 2 H from
        QuotientGroup.eq_one_iff _]
  constructor
  · intro h
    exact mem_map.mpr ⟨⟨x, liftStar_le H P x.property⟩, h, rfl⟩
  · rintro ⟨y, hy, he⟩
    have he' : y = ⟨x, liftStar_le H P x.property⟩ := Subtype.ext he
    exact he' ▸ hy

/-- The actual kernel is a two-group; ambient normality of H is unnecessary. -/
theorem liftStarMap_kernel_isTwoGroup (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    IsPGroup 2 (liftStarMap H P).ker := by
  rw [liftStarMap_kernel]
  exact (isPGroup_pCoreIn 2 H).comap_subtype

variable [Finite G]

/-- Solvability lifts because the quotient map has a two-group kernel. -/
theorem liftStar_solvable (H : Subgroup G) (P : Subgroup (Source.Hstar H))
    [Group.IsSolvable P] : Group.IsSolvable (liftStar H P) := by
  let f := liftStarMap H P
  let : Group.IsNilpotent f.ker := (liftStarMap_kernel_isTwoGroup H P).isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- The uniform solvable-overgroup assertion in 13.8.13 applies to the
constructed preimage, after its model has supplied solvability. -/
theorem solvable_liftStar_le_M (L₁ T G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (P : Subgroup (Source.Hstar H)) [Group.IsSolvable P]
    (hbase : Source.starImage H (L₁ ⊔ T) ≤ P) : liftStar H P ≤ M :=
  hex (liftStar H P) ((le_liftStar_iff H _ hH.1.2 P).mpr hbase)
    ((liftStar_le H P).trans hH.2.1) (liftStar_solvable H P)

/-- Taking the intrinsic two-core quotient commutes with this full preimage.
This preserves the actual source of the quotient rather than choosing a
new abstract group of the same order. -/
noncomputable def liftStarQuotientEquiv (H : Subgroup G) (P : Subgroup (Source.Hstar H)) :
    (liftStar H P ⧸ pCore 2 (liftStar H P)) ≃* (P ⧸ pCore 2 P) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := liftStarMap H P
  let q := (QuotientGroup.mk' (pCore 2 P)).comp f
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (liftStarMap_surjective H P)
  have hker : q.ker = pCore 2 (liftStar H P) := by
    change ((QuotientGroup.mk' (pCore 2 P)).comp f).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup (liftStarMap_surjective H P)
      (liftStarMap_kernel_isTwoGroup H P)
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

/-- The quotient equivalence retains the natural representatives. -/
theorem liftStarQuotientEquiv_mk (H : Subgroup G) (P : Subgroup (Source.Hstar H))
    (x : liftStar H P) :
    liftStarQuotientEquiv H P (QuotientGroup.mk' (pCore 2 (liftStar H P)) x) =
      QuotientGroup.mk' (pCore 2 P) (liftStarMap H P x) := by
  rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
