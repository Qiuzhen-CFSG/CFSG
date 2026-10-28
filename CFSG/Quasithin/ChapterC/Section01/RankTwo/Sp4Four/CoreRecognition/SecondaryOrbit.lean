module
public import Theory.Representation.SymplecticFourConjugationSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Basic
public import Theory.Frattini.FiniteIntersection
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Injective

/-!
# The terminal secondary-orbit argument in source (3.6)

The source subgroups R_alpha and R_alpha' are the actual local conjugate
spans of their elementary seeds. Disjoint ambient Frattini images make their
common commutator elementary. Its central supplement contains the kernel of
the specified natural section, so the kernel is elementary too. Conjugate
generation supplies a nonzero seed in that section; natural-vector
transitivity forces R_alpha itself to be elementary and centralize its seed.

This proves the last implication on MS93 printed p.871. The preceding source
construction of the natural section, kernel placement and paired Frattini
bounds remains explicit. No equality with the intrinsic block core is used,
and the fixed central attachment is retained throughout.
-/

public section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {G F : Type*} [Group G] [Field F] [Algebra (ZMod 2) F]

private theorem seed_le_span (Y H : Subgroup G) : Y ≤ conjugatesIn Y H := by
  have hh := le_iSup (fun h : H => rightConjugate Y h) (1:H)
  intro y hy
  apply hh
  exact ⟨y,hy,by simp⟩

/-- The source orbit seed cannot disappear in the natural quotient. -/
theorem secondary_seed_not_le_kernel (H Y D : Subgroup G)
    (q : H →* Sp F)
    (d : BinaryConjugationSection H (conjugatesIn Y H) D
      ((restrictScalars (k := ZMod 2) (symplecticNatural 2)).comp q)) : ¬ Y ≤ D := by
  intro hYD
  have hspan : conjugatesIn Y H ≤ D := by
    apply iSup_le
    intro h
    rintro _ ⟨y,hy,rfl⟩
    let v : conjugatesIn Y H := ⟨y,seed_le_span Y H hy⟩
    have hv : d.coordinates v = 1 := (d.coordinates_eq_one_iff v).mpr (hYD hy)
    have hh := d.equivariant h⁻¹ v
    rw [hv] at hh
    have hz : d.coordinates ⟨(h⁻¹:G)*v*(h⁻¹:G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized h⁻¹.property) v).mp v.property⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hh
    exact (d.coordinates_eq_one_iff _).mp hz
  obtain ⟨v,hv⟩ := d.onto (Multiplicative.ofAdd (e 0))
  have hz := (d.coordinates_eq_one_iff v).mpr (hspan v.property)
  rw [hv] at hz
  have hh := congrFun (congrArg Multiplicative.toAdd hz) (.inl 0)
  simp [Theory.SpecificGroups.SymplecticFour.e] at hh

/-- The actual secondary orbit in the symplectic branch of source3.6. -/
noncomputable abbrev secondaryOrbit {M : Type*} [Group M] (R : Subgroup M)
    (a : Vertex R) (Y : Subgroup (FreeAmalgam R)) := conjugatesIn Y (stabilizer R a)

/-- The paired Frattini calculation and natural coordinates force the source
secondary orbit to centralize its original elementary seed. -/
theorem secondary_orbit_centralizes_seed {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (geometry : Geometry R) (a a' : Vertex R)
    (ha : color R a = false) (ha' : color R a' = false)
    (hb : 0 < geometry.b R)
    (Y X D : Subgroup (FreeAmalgam R))
    (hY : Y ≤ Z R a') (hX : X ≤ stabilizer R a')
    (q : stabilizer R a →* Sp F) (hq : Function.Surjective q)
    (d : BinaryConjugationSection (stabilizer R a) (secondaryOrbit R a Y) D
      ((restrictScalars (k := ZMod 2) (symplecticNatural 2)).comp q))
    (htwo : IsPGroup 2 (secondaryOrbit R a Y))
    (htwo' : IsPGroup 2 (secondaryOrbit R a' X))
    (hcross : ⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ ≤ secondaryOrbit R a Y)
    (hcross' : ⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ ≤ secondaryOrbit R a' X)
    (hphi : Disjoint
      ((frattini (secondaryOrbit R a Y)).map (secondaryOrbit R a Y).subtype)
      ((frattini (secondaryOrbit R a' X)).map (secondaryOrbit R a' X).subtype))
    (hD : D ≤ ⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ ⊔ Z R a)
    (hZ : Z R a ≤ centralizer (secondaryOrbit R a Y : Set (FreeAmalgam R)))
    (hcentral : D ≤ centralizer (secondaryOrbit R a Y : Set (FreeAmalgam R))) :
    ⁅secondaryOrbit R a Y,Y⁆ = ⊥ := by
  let := finite_stabilizer R a
  let := finite_stabilizer R a'
  let : Finite (secondaryOrbit R a Y) :=
    Finite.of_injective (inclusion d.section_le) (inclusion_injective _)
  let : Finite (secondaryOrbit R a' X) :=
    Finite.of_injective (inclusion (conjugatesIn_le X (stabilizer R a') hX))
      (inclusion_injective _)
  have hba : 0 < criticalDistance R a (geometry.exists_critical a ha) := by
    rw [criticalDistance_eq_base R a ha (geometry.exists_critical a ha)
      (geometry.exists_critical (alpha R) rfl)]
    exact hb
  have hba' : 0 < criticalDistance R a' (geometry.exists_critical a' ha') := by
    rw [criticalDistance_eq_base R a' ha' (geometry.exists_critical a' ha')
      (geometry.exists_critical (alpha R) rfl)]
    exact hb
  let := Z_elementary_of_positive R geometry a ha hba
  let := Z_elementary_of_positive R geometry a' ha' hba'
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective (inclusion hY) (inclusion_injective _)
  let : IsElementaryAbelian 2 (⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ : Subgroup (FreeAmalgam R)) :=
    finite_common_subgroup_elementary_of_disjoint_frattini htwo htwo' hcross hcross' hphi
  let : IsElementaryAbelian 2 (⁅secondaryOrbit R a Y,secondaryOrbit R a' X⁆ ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    IsElementaryAbelian.sup_of_le_centralizer (hZ.trans (centralizer_le hcross))
  let : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.of_injective (inclusion hD) (inclusion_injective _)
  let : IsElementaryAbelian 2 (secondaryOrbit R a Y) :=
    d.elementary_of_natural_symplectic q hq hcentral Y (seed_le_span Y _)
      (secondary_seed_not_le_kernel _ _ _ q d)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro u hu y hy
  have he := (IsMulCommutative.is_comm (M := secondaryOrbit R a Y)).comm
    ⟨y,seed_le_span Y _ hy⟩ ⟨u,hu⟩
  exact congrArg Subtype.val he
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
