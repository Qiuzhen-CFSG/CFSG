module
public import Stellmacher.SectionOne.OneSevenFactorDefs
public import Theory.GroupAction.CoprimeHall

/-!
# Action support of the factors in (1.7)

Each local SL2 factor has the same four-element commutator module as its
derived C3. The coprime decomposition for that C3 supplies a complementary
fixed space, and the full factor fixes that complement: the difference of
an image and its original vector lies in both complementary subgroups.

Normality of the factor in its join with the odd core makes the derived C3
normal in the odd core. It therefore lies in the characteristic 3-core of
the odd core, whose ambient image is a normal 3-subgroup of G. This places
the derived subgroup in O3(G), as required to apply (1.4) to pairs of factors.

These are the support and core facts behind the global Ω-star product in
Stellmacher (1.7), journal p.19, refs/latex/stellmacher-n-group.tex.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem derived_normalizer {G : Type u} [Group G] (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (((commutator D).map D.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.map_subtype_commutator]
  intro g hg
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator, hmap]

/-- The odd core normalizes each factor's derived C3. -/
public theorem oneSevenFactor_oddCore_normalizes_derived
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) :
    oddCore G ≤ Subgroup.normalizer (((commutator D).map D.subtype : Subgroup G) : Set G) := by
  have hWD : oddCore G ≤ Subgroup.normalizer (D : Set G) :=
    (show oddCore G ≤ oddCore G ⊔ D from le_sup_left).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp hD.2.2.2)
  exact hWD.trans (derived_normalizer D)

/-- The derived C3 of a one-seven factor lies in the ambient 3-core. -/
public theorem oneSevenFactor_derived_le_threeCore
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) :
    (commutator D).map D.subtype ≤ pCore 3 G := by
  let W : Subgroup G := oddCore G
  let F : Subgroup G := (commutator D).map D.subtype
  have hFW : F ≤ W := hD.2.1.1
  have hWF : W ≤ Subgroup.normalizer (F : Set G) :=
    oneSevenFactor_oddCore_normalizes_derived D hD
  let _ : W.Normal := pPrimeCore_normal
  let _ : (F.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFW).mpr hWF
  have hFp : IsPGroup 3 F := IsPGroup.of_card (n := 1) (by simpa [F] using hD.2.1.2.1)
  have hFsubp : IsPGroup 3 (F.subgroupOf W) :=
    hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hFW).symm
  have hle : F.subgroupOf W ≤ pCore 3 W := le_sSup ⟨inferInstance, hFsubp⟩
  have hmap := Subgroup.map_mono (f := W.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hFW] at hmap
  have hcoreNormal : ((pCore 3 W).map W.subtype).Normal := inferInstance
  exact hmap.trans (le_sSup ⟨hcoreNormal, (pCore_isPGroup (p := 3) (G := W)).map W.subtype⟩)

private theorem action_commutator_mono
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {D E : Subgroup G} (hDE : D ≤ E) :
    commutatorAction D V ≤ commutatorAction E V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro z ⟨d, v, rfl⟩
  exact ⟨⟨d, hDE d.property⟩, v, rfl⟩

/-- The full action commutator equals its derived C3 action commutator. -/
public theorem oneSevenFactor_full_commutator_eq_derived
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) :
    commutatorAction D V = commutatorAction ((commutator D).map D.subtype) V := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
    (action_commutator_mono (Subgroup.map_subtype_le _))
  rw [hD.2.2.1, hD.2.1.2.2]

private theorem derived_coprime_module
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D : Subgroup G) (hD : IsOneSevenFactor (V := V) D) :
    Nat.Coprime (Nat.card ((commutator D).map D.subtype)) (Nat.card V) := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  rw [hD.2.1.2.1, hn]
  exact (show Nat.Coprime 3 2 by decide).pow_right n

/-- A one-seven factor fixes the complementary fixed space of its derived C3. -/
public theorem oneSevenFactor_fixes_derived_fixedPoints
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (d : G) (hd : d ∈ D) (v : V)
    (hv : v ∈ FixedPoints.subgroup ((commutator D).map D.subtype) V) :
    d • v = v := by
  let F : Subgroup G := (commutator D).map D.subtype
  let C : Subgroup V := FixedPoints.subgroup F V
  have hnorm : D ≤ Subgroup.normalizer (F : Set G) :=
    D.le_normalizer.trans (derived_normalizer D)
  have hdv : d • v ∈ C := by
    rw [FixedPoints.mem_subgroup]
    intro f
    have hconj : d⁻¹ * (f : G) * d ∈ F := by
      have hi := (Subgroup.mem_normalizer_iff.mp (hnorm (D.inv_mem hd))) (f : G)
      simpa using hi.mp f.property
    have hf := (FixedPoints.mem_subgroup (M := F) (a := v)).mp hv ⟨_, hconj⟩
    change (f : G) • (d • v) = d • v
    calc
      (f : G) • (d • v) = d • ((d⁻¹ * (f : G) * d) • v) := by
        simp only [← mul_smul]
        congr 1
        group
      _ = d • v := by rw [show (d⁻¹ * (f : G) * d) • v = v from hf]
  have hdelta : v⁻¹ * (d • v) ∈ commutatorAction F V := by
    rw [← oneSevenFactor_full_commutator_eq_derived D hD, commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨(⟨d, hd⟩ : D), v, rfl⟩
  have hdeltaC : v⁻¹ * (d • v) ∈ C := C.mul_mem (C.inv_mem hv) hdv
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := F)
    (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
    (derived_coprime_module D hD) (inferInstance : IsMulCommutative V)
  have hone : v⁻¹ * (d • v) = 1 := hcompl.disjoint.le_bot ⟨hdeltaC, hdelta⟩
  exact (inv_mul_eq_one.mp hone).symm

end Stellmacher.SectionOne
