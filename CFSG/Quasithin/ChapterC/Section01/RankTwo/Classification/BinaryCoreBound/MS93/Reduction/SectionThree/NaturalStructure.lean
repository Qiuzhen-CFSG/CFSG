module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LocalLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian
public import Theory.SpecificGroups.PSL3Two.OuterInvolutionSinger

/-!
# Assembly of the binary natural structure from the source 3.8 output

A natural moving group has no residual-fixed element: its marked quotient
contains a Singer element acting without fixed vectors. Once X splits as
its moving group and residual-fixed subgroup, the literal omega-center
argument gives X = Z, at the base vertex and hence at every M-vertex.
These facts supply all fields of `BinaryNaturalStructure`.

`LocalSource.binaryNaturalStructure` constructs this structure for b > 2.
The binary alternatives retain both the doubled and nonsplit possibilities.
Each bad alternative forces distance four and residual-fixed derived radius.
The moving-radius representation theorem then proves V_a^circ abelian;
the three-subgroups argument forces an abelian radius, contradicting critical
noncommutation. Thus the natural/split alternative holds, with an actual
equivariant model of U and one marking of the specified quotient.

Source: Meierfrankenfeld--Stellmacher (1993), pp.863--868, 877--882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem singer_fixed_eq_zero (v : Fin 3 → ZMod 2)
    (hv : Matrix.PSL3Two.OuterInvolutionSinger.singer.val.mulVec v = v) : v = 0 := by
  have h : ∀ w : Fin 3 → ZMod 2,
      Matrix.PSL3Two.OuterInvolutionSinger.singer.val.mulVec w = w → w = 0 := by decide
  exact h v hv

/-- The actual natural moving group has trivial intersection with the fixed
part. No splitting of Z or of X is used in this assertion. -/
theorem NaturalU.disjoint_fixed {source : LocalSource L R}
    (natural : NaturalU R source.projection) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    Disjoint (U R (alpha R))
      (Z R (alpha R) ⊓ Subgroup.centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  let u : U R (alpha R) := ⟨x, hx.1⟩
  have hZX := geometry.omega_bound (alpha R) rfl hb
  have hcentral : x ∈ Subgroup.centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) :=
    ((source.X_fixed_eq_stabilizer_fixed (alpha R) rfl).le ⟨hZX hx.2.1, hx.2.2⟩).2
  obtain ⟨m, hm⟩ := source.projection_surjective
    (natural.marking.symm Matrix.PSL3Two.OuterInvolutionSinger.singer)
  have hact := natural.action m u u (by
    have hmS : embedM R m ∈ stabilizer R (alpha R) := by
      rw [alpha, stabilizer_m_base]
      exact ⟨m, rfl⟩
    change x = embedM R m * x * (embedM R m)⁻¹
    rw [hcentral _ hmS, mul_inv_cancel_right])
  rw [hm, MulEquiv.apply_symm_apply] at hact
  have hzero := singer_fixed_eq_zero _ hact.symm
  have hone : natural.equiv u = 1 := congrArg Multiplicative.ofAdd hzero
  have hu : u = 1 := natural.equiv.injective (hone.trans natural.equiv.map_one.symm)
  exact congrArg Subtype.val hu

/-- The source 3.8 natural/split alternative implies the exact published
natural-structure output. Both nontrivial source premises remain explicit. -/
theorem LocalSource.binaryNaturalStructure_of_X_decomposition
    (source : LocalSource L R) (geometry : Geometry R) (hb : 0 < geometry.b R)
    (natural : NaturalU R source.projection)
    (hsplit : X R (alpha R) = U R (alpha R) ⊔
      (X R (alpha R) ⊓ Subgroup.centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)))) :
    Nonempty (BinaryNaturalStructure source) := by
  have hbase := source.X_eq_Z_of_decomposition geometry hb (alpha R) rfl hsplit
  refine ⟨{
    X_eq_Z := ?_
    natural := natural
    decomposition := ?_
    disjoint := natural.disjoint_fixed geometry hb }⟩
  · intro a ha
    obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
    have hx := edgeOmega_act R g (alpha R)
    have hz := Z_act R g (alpha R)
    change X R (act R g (alpha R)) = (X R (alpha R)).map _ at hx
    simp only [alpha, act_mVertex, one_mul] at hx hz
    rw [hx, hz]
    exact congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
  · simpa only [hbase] using hsplit

/-- The natural structure is unconditional away from critical distance four:
all three bad binary module branches force that distance. -/
theorem LocalSource.binaryNaturalStructure_of_distance_ne_four
    (source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hne : geometry.b R ≠ 4) : Nonempty (BinaryNaturalStructure source) := by
  rcases ModuleAlternatives.alternatives source geometry (by omega) with hnatural | hbad
  · obtain ⟨⟨natural⟩, hsplit, _⟩ := hnatural
    apply source.binaryNaturalStructure_of_X_decomposition geometry (by omega) natural
    simpa only [ModuleAlternatives.fixedPart, sup_comm] using hsplit
  · exact (hne (NaturalStructure.Exclusion.distance_eq_four source geometry hb hbad)).elim

/-- Natural-structure assembly from the radius representation step in source
(3.8). Its explicit abelianness premise is discharged in
`LocalSource.binaryNaturalStructure`. -/
theorem LocalSource.binaryNaturalStructure_of_bad_moving_commutative
    (source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hmoving : ModuleAlternatives.BadCase source →
      ∀ a, color R a = false → IsMulCommutative (Vcirc R a)) :
    Nonempty (BinaryNaturalStructure source) := by
  rcases ModuleAlternatives.alternatives source geometry (by omega) with hnatural | hbad
  · obtain ⟨⟨natural⟩, hsplit, _⟩ := hnatural
    apply source.binaryNaturalStructure_of_X_decomposition geometry (by omega) natural
    simpa only [ModuleAlternatives.fixedPart, sup_comm] using hsplit
  · have hfour := NaturalStructure.Exclusion.distance_eq_four source geometry hb hbad
    obtain ⟨a', hc⟩ := criticalPair_exists R (alpha R) (geometry.exists_critical (alpha R) rfl)
    have hd : (cosetGraph R).dist (alpha R) a' = 4 :=
      (hc.1.trans (geometry.distance_constant (alpha R) rfl)).trans hfour
    obtain ⟨c, hca', hac⟩ := CriticalCriterion.exists_two_before R (alpha R) a' (by omega)
    have hac2 : (cosetGraph R).dist (alpha R) c = 2 := by omega
    have hcColor : color R c = false := by
      obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist (alpha R) c
      have hh := (walk_even_iff_color_eq R p).mp (by rw [hp, hac2]; decide)
      exact hh.symm
    obtain ⟨t, _, hct⟩ := exists_common_neighbor_of_dist_two R (alpha R) c hac2
    have hfixed := NaturalStructure.Exclusion.radius_derived_le_fixed source geometry hb hbad c hcColor
    have hcentral := NaturalStructure.Exclusion.moving_central_of_commutative source geometry hb
      c hcColor hfixed (hmoving hbad c hcColor)
    have hcomm := NaturalStructure.Exclusion.radius_commutative_of_moving_central source geometry hb
      c t hcColor hct hcentral
    exact (NaturalStructure.Exclusion.critical_midpoint_radius_not_commutative source geometry
      (alpha R) rfl a' hc c hac2 hca' hcomm).elim

/-- The binary natural structure from MS93 (3.8) and (4.1): X = Z at every
M-vertex, and at the base vertex Z is the direct product of its actual marked
natural moving subgroup U and its residual-fixed subgroup. All bad module
alternatives are excluded using the derived-radius and moving-radius theorems. -/
theorem LocalSource.binaryNaturalStructure
    (source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R) :
    Nonempty (BinaryNaturalStructure source) := by
  apply source.binaryNaturalStructure_of_bad_moving_commutative geometry hb
  intro hbad a ha
  exact NaturalStructure.Exclusion.moving_commutative_of_badCase_of_derived_fixed
    source geometry hb hbad a ha
    (NaturalStructure.Exclusion.radius_derived_le_fixed source geometry hb hbad a ha)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
