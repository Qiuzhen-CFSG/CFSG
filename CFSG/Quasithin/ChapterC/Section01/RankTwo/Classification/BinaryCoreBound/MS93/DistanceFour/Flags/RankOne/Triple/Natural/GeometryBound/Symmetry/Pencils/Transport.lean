module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils.Model
/-!
# Transporting a finite pencil selection to the original amalgam

Local flag cores are the embedded full preimages of the literal matrix cores.
Coset incidence lifts along the original surjection. The supplied natural
isomorphism, with its arbitrary marking unchanged, identifies the moving
layer's fixed vectors and detects unequal source fixed subgroups.

Generation by three quotient cores lifts to generation of the whole vertex
stabilizer because all three preimages contain the projection kernel. Thus
centralizing those actual cores is enough for centrality in the full
stabilizer, including the fixed complement in the source Z-layer.

The final selection is conditional on `MatrixSeparation`; this module does
not assert a constructor for that finite matrix obligation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.905.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem map_conj_comap {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup H) (g : G) :
    (A.comap f).map (MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj (f g)).toMonoidHom).comap f := by
  ext x
  simp only [mem_map_equiv, mem_comap]
  change f (g⁻¹ * x * g) ∈ A ↔ (f g)⁻¹ * f x * f g ∈ A
  simp only [map_mul, map_inv]

private theorem map_conj_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup G) (g : G) :
    (A.map f).map (MulAut.conj (f g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map f := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

/-- Every local core is the full matrix-core preimage in the original embedding. -/
theorem localFlagKernel_eq_matrix_preimage (source : LocalSource L R) (i : Bool) (g : M) :
    localFlagKernel source i g =
      ((matrixCore source.flag i (source.projection g)).comap source.projection).map
        (embedM R) := by
  change (((parabolic source.projection source.flag i).pCoreIn 2).map (embedM R)).map
    (MulAut.conj (embedM R g)).toMonoidHom = _
  rw [map_conj_map, Incident.parabolic_core_eq_comap, map_conj_comap]
  rfl

omit [Finite M] in
/-- The original left-coset incidence is exactly incidence under the source projection. -/
theorem flagIncident_iff_matrix (source : LocalSource L R) (i : Bool) (g d : M) :
    flagIncident source i g d ↔
      matrixIncident source.flag i (source.projection g) (source.projection d) := by
  constructor
  · rintro ⟨m,hm,hn⟩
    refine ⟨source.projection m, ?_, ?_⟩
    · change source.projection (g⁻¹*m) ∈ modelParabolic source.flag i at hm
      simpa only [map_mul, map_inv] using hm
    · change source.projection (d⁻¹*m) ∈ modelParabolic source.flag (!i) at hn
      simpa only [map_mul, map_inv] using hn
  · rintro ⟨a,ha,hb⟩
    obtain ⟨m,rfl⟩ := source.projection_surjective a
    refine ⟨m, ?_, ?_⟩
    · change source.projection (g⁻¹ * m) ∈ modelParabolic source.flag i
      simpa only [map_mul, map_inv] using ha
    · change source.projection (d⁻¹ * m) ∈ modelParabolic source.flag (!i)
      simpa only [map_mul, map_inv] using hb

/-- The incident core intersection retains the full projection kernel. -/
theorem kernel_intersection_eq_matrix_preimage (source : LocalSource L R)
    (i : Bool) (d : M) :
    flagKernel source i ⊓ localFlagKernel source (!i) d =
      ((matrixCore source.flag i 1 ⊓ matrixCore source.flag (!i) (source.projection d)).comap
        source.projection).map (embedM R) := by
  have hbase : flagKernel source i = localFlagKernel source i 1 :=
    (localConjugate_one _).symm
  rw [hbase, localFlagKernel_eq_matrix_preimage, localFlagKernel_eq_matrix_preimage,
    map_one, ← map_inf _ _ _ (embedM_injective R), ← comap_inf]

/-- The source relative index is the order of the actual matrix-core intersection. -/
theorem intersection_index_eq_matrix_card (source : LocalSource L R) (i : Bool) (d : M) :
    (Q R (alpha R)).relIndex (flagKernel source i ⊓ localFlagKernel source (!i) d) =
      Nat.card ↥(matrixCore source.flag i 1 ⊓
        matrixCore source.flag (!i) (source.projection d)) := by
  rw [kernel_intersection_eq_matrix_preimage, Q_alpha R source.two_group source.core_le,
    relIndex_map_map_of_injective _ _ (embedM_injective R), ← source.projection_kernel,
    relIndex_ker, map_comap_eq_self_of_surjective source.projection_surjective]


open RankOnePairing.Incidence.FixedGeometry.ValueConstruction

/-- The supplied equivariant isomorphism identifies actual fixed vectors, with its marking unchanged. -/
theorem natural_mem_localFlagZ_iff (source : LocalSource L R)
    (natural : NaturalU R source.projection) (i : Bool) (g : M) (u : U R (alpha R)) :
    (u : FreeAmalgam R) ∈ localFlagZ source i g ↔
      natural.equiv u ∈ matrixFixed natural.marking source.flag i (source.projection g) := by
  constructor
  · intro hu
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨m,rfl⟩ := source.projection_surjective a
    have hm : embedM R m ∈ localFlagKernel source i g := by
      rw [localFlagKernel_eq_matrix_preimage]
      exact mem_map_of_mem _ ha
    have hc := hu.2 _ hm
    have he : (u : FreeAmalgam R) = embedM R m * u * (embedM R m)⁻¹ := by
      rw [hc]
      group
    exact (natural.action m u u he).symm
  · intro hu
    refine ⟨DistanceEight.U_le_Z R _ u.property, ?_⟩
    intro y hy
    rw [localFlagKernel_eq_matrix_preimage] at hy
    obtain ⟨m,hm,rfl⟩ := hy
    have hfix : vectorAction (natural.marking (source.projection m)) (natural.equiv u) =
        natural.equiv u := hu _ (mem_map_of_mem _ hm)
    let v : U R (alpha R) := ⟨_, le_normalizer_iff.mp natural.normalized
      _ (show embedM R m ∈ Mbar R from ⟨m,rfl⟩) _ u.property⟩
    have he : v = u := natural.equiv.injective ((natural.action m u v rfl).trans hfix)
    have hc : embedM R m * (u : FreeAmalgam R) * (embedM R m)⁻¹ = u :=
      congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul.mp hc)

/-- Distinct marked matrix fixed spaces force distinct source fixed Z-layers. -/
theorem localFlagZ_ne_of_matrixFixed_ne (source : LocalSource L R)
    (natural : NaturalU R source.projection) (i : Bool) (g h : M)
    (hne : matrixFixed natural.marking source.flag i (source.projection g) ≠
      matrixFixed natural.marking source.flag i (source.projection h)) :
    localFlagZ source i g ≠ localFlagZ source i h := by
  intro he
  apply hne
  ext v
  obtain ⟨u,rfl⟩ := natural.equiv.surjective v
  rw [← natural_mem_localFlagZ_iff, ← natural_mem_localFlagZ_iff, he]

/-- Generation by the three quotient cores lifts to generation of G_alpha,
since each actual core already contains the kernel of the source projection. -/
theorem localFlagKernel_sup_eq_stabilizer (source : LocalSource L R)
    (i : Bool) (g g' : M)
    (hgen : (matrixCore source.flag i 1 ⊔ matrixCore source.flag i (source.projection g)) ⊔
      matrixCore source.flag i (source.projection g') = ⊤) :
    (flagKernel source i ⊔ localFlagKernel source i g) ⊔ localFlagKernel source i g' =
      stabilizer R (alpha R) := by
  let A := (matrixCore source.flag i 1).comap source.projection
  let B := (matrixCore source.flag i (source.projection g)).comap source.projection
  let C := (matrixCore source.flag i (source.projection g')).comap source.projection
  have hmap : ((A ⊔ B) ⊔ C).map source.projection = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_sup]
    dsimp only [A,B,C]
    rw [map_comap_eq_self_of_surjective source.projection_surjective,
      map_comap_eq_self_of_surjective source.projection_surjective,
      map_comap_eq_self_of_surjective source.projection_surjective]
    exact hgen
  have hker : source.projection.ker ≤ (A ⊔ B) ⊔ C :=
    (MonoidHom.ker_le_comap _ _).trans (le_sup_left.trans le_sup_left)
  have htop : (A ⊔ B) ⊔ C = ⊤ := by
    have hh := congrArg (Subgroup.comap source.projection) hmap
    rwa [comap_map_eq_self hker, comap_top] at hh
  have hbase : flagKernel source i = localFlagKernel source i 1 :=
    (localConjugate_one _).symm
  rw [hbase, localFlagKernel_eq_matrix_preimage, localFlagKernel_eq_matrix_preimage,
    localFlagKernel_eq_matrix_preimage, map_one, ← Subgroup.map_sup, ← Subgroup.map_sup]
  change ((A ⊔ B) ⊔ C).map (embedM R) = _
  rw [htop, ← MonoidHom.range_eq_map, alpha, stabilizer_m_base]
  rfl

/-- No natural-module complement is discarded: the full generated stabilizer
centralizes every element in the displayed triple intersection. -/
theorem triple_le_center_of_generation (source : LocalSource L R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (g g' : M)
    (hgen : (matrixCore source.flag i 1 ⊔ matrixCore source.flag i (source.projection g)) ⊔
      matrixCore source.flag i (source.projection g') = ⊤) :
    localFlagZ source i g' ⊓ localFlagZ source i g ⊓ Z R (beta R) ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  intro x hx
  have hbase : x ∈ localFlagZ source i 1 := by
    have hh := localConjugate_edgeZ_le_localFlagZ source i hkernel 1
    rw [localConjugate_one] at hh
    exact hh hx.2
  have central (K : Subgroup (FreeAmalgam R))
      (h : x ∈ centralizer (K : Set (FreeAmalgam R))) :
      K ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
    intro y hy z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (h y hy).symm
  have h1 : flagKernel source i ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
    have hh := central _ hbase.2
    simpa only [localFlagKernel, localConjugate_one] using hh
  have h2 := central _ hx.1.2.2
  have h3 := central _ hx.1.1.2
  have hall := sup_le (sup_le h1 h2) h3
  rw [localFlagKernel_sup_eq_stabilizer source i g g' hgen] at hall
  refine ⟨⟨x, Z_le_stabilizer R _ hbase.1⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  exact Subtype.ext ((hall y.property x (Set.mem_singleton x)).symm)


/-- Lifting a concrete matrix selection supplies the source flag separation.
This statement remains conditional until MatrixSeparation has been constructed. -/
theorem separate_of_matrixSeparation (source : LocalSource L R)
    (natural : NaturalU R source.projection) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hmat : MatrixSeparation natural.marking source.flag i)
    (d d' : M) (hd : flagIncident source i 1 d) (hd' : flagIncident source i 1 d')
    (hne : flagKernel source i ⊓ localFlagKernel source (!i) d ≠
      flagKernel source i ⊓ localFlagKernel source (!i) d') :
    ∃ g g' : M, flagIncident source i g d ∧ flagIncident source i g' d' ∧
      localFlagZ source i g ≠ localFlagZ source i 1 ∧
      localFlagZ source i g' ≠ localFlagZ source i 1 ∧
      localFlagZ source i g' ⊓ localFlagZ source i g ⊓ Z R (beta R) ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  have hdm : matrixIncident source.flag i 1 (source.projection d) := by
    simpa only [map_one] using (flagIncident_iff_matrix source i 1 d).mp hd
  have hdm' : matrixIncident source.flag i 1 (source.projection d') := by
    simpa only [map_one] using (flagIncident_iff_matrix source i 1 d').mp hd'
  have hnem : matrixCore source.flag i 1 ⊓ matrixCore source.flag (!i) (source.projection d) ≠
      matrixCore source.flag i 1 ⊓ matrixCore source.flag (!i) (source.projection d') := by
    intro he
    apply hne
    rw [kernel_intersection_eq_matrix_preimage, kernel_intersection_eq_matrix_preimage, he]
  obtain ⟨a,a',ha,ha',hna,hna',hgen⟩ := hmat.separate _ _ hdm hdm' hnem
  obtain ⟨g,rfl⟩ := source.projection_surjective a
  obtain ⟨g',rfl⟩ := source.projection_surjective a'
  refine ⟨g,g', (flagIncident_iff_matrix source i g d).mpr ha,
    (flagIncident_iff_matrix source i g' d').mpr ha', ?_, ?_,
    triple_le_center_of_generation source i hkernel g g' hgen⟩
  · apply localFlagZ_ne_of_matrixFixed_ne source natural i g 1
    simpa only [map_one] using hna
  · apply localFlagZ_ne_of_matrixFixed_ne source natural i g' 1
    simpa only [map_one] using hna'

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
