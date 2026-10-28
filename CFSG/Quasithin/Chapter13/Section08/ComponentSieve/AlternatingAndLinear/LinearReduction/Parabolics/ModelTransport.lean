module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OvergroupLift

/-!
# Marked model subgroups in the actual star quotient

A fixed equivalence H/O₂(H) ≃ B pulls concrete subgroups of B back to
subgroups of H. The quotient map has exactly the restricted O₂(H) kernel.
Its induced two-core quotient equivalence preserves representatives and
all embedded source subgroups. Strict enlargement of the actual overlap
H ∩ M therefore gives a member of the literal source family Hz.

These transport results connect the constructed binary parabolics and Levi
maps to Aschbacher–Smith 13.8.25, printed pp.959–960 (PDF pp.976–977),
combined manuscript of 1 March 2004. No flag position or source subgroup
identification is asserted by this transport alone.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

variable {G B : Type*} [Group G] [Group B]

/-- Restrict the given model equivalence to the full inverse image of a subgroup. -/
noncomputable def modelSubgroupEquiv (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) : P.comap e.toMonoidHom ≃* P :=
  MulEquiv.ofBijective (e.toMonoidHom.subgroupComap P)
    ⟨fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)),
      e.toMonoidHom.subgroupComap_surjective_of_surjective P e.surjective⟩

/-- Full preimage in H of a subgroup in the prescribed concrete model of H*. -/
def modelLift (H : Subgroup G) (e : Source.Hstar H ≃* B) (P : Subgroup B) :
    Subgroup G := liftStar H (P.comap e.toMonoidHom)

theorem modelLift_le (H : Subgroup G) (e : Source.Hstar H ≃* B) (P : Subgroup B) :
    modelLift H e P ≤ H := liftStar_le H _

theorem modelLift_starImage (H : Subgroup G) (e : Source.Hstar H ≃* B) (P : Subgroup B) :
    (Source.starImage H (modelLift H e P)).map e.toMonoidHom = P := by
  rw [modelLift, starImage_liftStar, map_comap_eq_self_of_surjective e.surjective]

theorem le_modelLift_iff (H A : Subgroup G) (hAH : A ≤ H)
    (e : Source.Hstar H ≃* B) (P : Subgroup B) :
    A ≤ modelLift H e P ↔ (Source.starImage H A).map e.toMonoidHom ≤ P := by
  rw [modelLift, le_liftStar_iff H A hAH, map_le_iff_le_comap]

theorem modelLift_lt_iff (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P Q : Subgroup B) : modelLift H e P < modelLift H e Q ↔ P < Q := by
  rw [modelLift, modelLift, liftStar_lt_iff]
  exact comap_lt_comap_of_surjective e.surjective

/-- The natural model map retains the chosen H* equivalence. -/
noncomputable def modelLiftMap (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) : modelLift H e P →* P :=
  (modelSubgroupEquiv H e P).toMonoidHom.comp (liftStarMap H (P.comap e.toMonoidHom))

theorem modelLiftMap_surjective (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) : Function.Surjective (modelLiftMap H e P) :=
  (modelSubgroupEquiv H e P).surjective.comp (liftStarMap_surjective H _)

theorem modelLiftMap_apply (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) (x : modelLift H e P) :
    (modelLiftMap H e P x : B) =
      e (QuotientGroup.mk' (pCore 2 H) ⟨x, modelLift_le H e P x.property⟩) := rfl

/-- Transport of an embedded source subgroup, with both subgroup markings retained. -/
theorem modelLiftMap_image (H A : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) (hA : A ≤ modelLift H e P) :
    (A.subgroupOf (modelLift H e P)).map (modelLiftMap H e P) =
      ((Source.starImage H A).map e.toMonoidHom).subgroupOf P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨⟨y, modelLift_le H e P y.property⟩, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, he⟩
    refine ⟨⟨y, hA hy⟩, hy, ?_⟩
    exact Subtype.ext he

theorem modelLiftMap_kernel (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) :
    (modelLiftMap H e P).ker = (Source.QH H).subgroupOf (modelLift H e P) := by
  exact (MonoidHom.ker_comp_of_injective (liftStarMap H (P.comap e.toMonoidHom))
    (modelSubgroupEquiv H e P).toMonoidHom (modelSubgroupEquiv H e P).injective).trans
      (liftStarMap_kernel H _)

theorem modelLiftMap_kernel_isTwoGroup (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) : IsPGroup 2 (modelLiftMap H e P).ker := by
  rw [modelLiftMap_kernel]
  exact (isPGroup_pCoreIn 2 H).comap_subtype

variable [Finite G]

/-- Intrinsic two-core quotients commute with the full preimage and model transport. -/
noncomputable def modelLiftQuotientEquiv (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) :
    (modelLift H e P ⧸ pCore 2 (modelLift H e P)) ≃* (P ⧸ pCore 2 P) :=
  (liftStarQuotientEquiv H (P.comap e.toMonoidHom)).trans
    (QuotientGroup.congr _ _ (modelSubgroupEquiv H e P)
      (pCore_map_iso 2 (modelSubgroupEquiv H e P)))

theorem modelLiftQuotientEquiv_mk (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) (x : modelLift H e P) :
    modelLiftQuotientEquiv H e P (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (modelLiftMap H e P x) := rfl

theorem modelLift_solvable (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) [Group.IsSolvable P] : Group.IsSolvable (modelLift H e P) := by
  let : Group.IsSolvable (P.comap e.toMonoidHom) :=
    Group.isSolvable_of_isSolvable_injective (f := (modelSubgroupEquiv H e P).toMonoidHom)
      (modelSubgroupEquiv H e P).injective
  exact liftStar_solvable H _

omit [Finite G] in
/-- Strict enlargement of the actual overlap lifts into Hz. -/
theorem modelLift_mem_Hz (L₁ T G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (e : Source.Hstar H ≃* B)
    (P Q : Subgroup B) (hbase : (Source.starImage H (L₁ ⊔ T)).map e.toMonoidHom ≤ Q)
    (hinter : modelLift H e P = H ⊓ M) (hPQ : P < Q) :
    modelLift H e Q ∈ Source.Hz L₁ T G₁ M := by
  apply liftStar_mem_Hz L₁ T G₁ M H hH (P.comap e.toMonoidHom) (Q.comap e.toMonoidHom)
    (map_le_iff_le_comap.mp hbase) hinter
  exact (liftStar_lt_iff H _ _).mp ((modelLift_lt_iff H e P Q).mpr hPQ)

section

variable {G B C : Type*} [Group G] [Group B] [Group C] [Finite G]

/-- Compute every marked source image under the composed concrete quotient map. -/
theorem modelLiftQuotientEquiv_image (H A : Subgroup G) (e : Source.Hstar H ≃* B)
    (P : Subgroup B) (a : (P ⧸ pCore 2 P) ≃* C) (hA : A ≤ modelLift H e P) :
    (A.subgroupOf (modelLift H e P)).map
      (((modelLiftQuotientEquiv H e P).trans a).toMonoidHom.comp (QuotientGroup.mk' _)) =
      (((Source.starImage H A).map e.toMonoidHom).subgroupOf P).map
        (a.toMonoidHom.comp (QuotientGroup.mk' _)) := by
  have hf : ((modelLiftQuotientEquiv H e P).trans a).toMonoidHom.comp (QuotientGroup.mk' _) =
      (a.toMonoidHom.comp (QuotientGroup.mk' _)).comp (modelLiftMap H e P) := by
    apply MonoidHom.ext
    intro x
    exact congrArg a (modelLiftQuotientEquiv_mk H e P x)
  rw [hf, ← map_map, modelLiftMap_image H A e P hA]

omit [Finite G] in
/-- Recover an actual subgroup from its model image when it contains O₂(H). -/
theorem modelLift_eq_of_image (H A : Subgroup G) (hAH : A ≤ H)
    (e : Source.Hstar H ≃* B) (P : Subgroup B)
    (himage : (Source.starImage H A).map e.toMonoidHom = P)
    (hcore : Source.QH H ≤ A) : modelLift H e P = A := by
  have hp : P.comap e.toMonoidHom = Source.starImage H A := by
    rw [← himage, comap_map_eq_self_of_injective e.injective]
  change liftStar H (P.comap e.toMonoidHom) = A
  rw [hp]
  exact liftStar_starImage_of_core_le H A hAH hcore

omit [Finite G] in
/-- The original normalizer restriction survives the fixed whole-group marking. -/
theorem model_normalizer_le (H : Subgroup G) (e : Source.Hstar H ≃* B)
    (A D : Subgroup (Source.Hstar H)) (R S : Subgroup B)
    (hA : A.map e.toMonoidHom = R) (hD : D.map e.toMonoidHom = S)
    (hn : normalizer (A : Set (Source.Hstar H)) ≤ normalizer (D : Set (Source.Hstar H))) :
    normalizer (R : Set B) ≤ normalizer (S : Set B) := by
  rw [← hA, ← hD, ← Subgroup.map_normalizer_eq_of_bijective A e.bijective,
    ← Subgroup.map_normalizer_eq_of_bijective D e.bijective]
  exact map_mono hn

end

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
