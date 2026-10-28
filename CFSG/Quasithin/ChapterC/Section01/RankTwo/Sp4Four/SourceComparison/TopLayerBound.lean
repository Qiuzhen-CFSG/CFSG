module
public import Theory.GroupTheory.Commutator.FixedSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.PlaneDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups

/-!
# The whole critical Z-layer bound from its moving natural section

The original Z-layer may have a trivial top beyond its moving cover. An
actor inner modulo its centralizer still moves that whole layer into U.
Commuting quotient actors and centralization of the critical commutator make
that displacement fixed by the critical actor. Its natural fixed plane is
covered by the original critical commutator, giving the source bound with
the complete moving kernel retained.

The inner-actor and plane-marking premises are explicit earlier inputs.
This route does not require a fixed supplement of Z or a central splitting.
Source: MS93 (3.3), first symplectic paragraph, printed p.867.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
variable {M : Type*} [Group M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}

/-- The critical actor normalizes the actual moving layer. -/
theorem critical_actor_normalizes_moving (path : CriticalPath R geometry a e) :
    Z R a ≤ normalizer (U R e : Set (FreeAmalgam R)) :=
  (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color)
    path.critical.1.le).trans (U_normalized e)

/-- The source displacement bound on the whole Z-layer from inner actors.
Only the moving layer has natural coordinates; no fixed supplement of Z
or splitting of the cover is required. -/
theorem critical_top_layer_bound_of_inner_actors
    (path : CriticalPath R geometry a e) (Y : Subgroup (FreeAmalgam R))
    {F : Type*} [Field F]
    (π : U R e →* Multiplicative (Vector F)) (α : Z R a →* Sp F)
    (hact : ∀ (z : Z R a) (u : U R e),
      π ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (α z • (π u).toAdd))
    (W : Submodule F (Vector F))
    (hfixed : ∀ v, (∀ z : Z R a, α z • v=v) → v ∈ W)
    (hcover : ∀ w ∈ W, ∃ d : ((⁅Z R a,Z R e⁆ ⊓ U R e) : Subgroup (FreeAmalgam R)),
      (π ⟨d.val,d.property.2⟩).toAdd = w)
    (hinner : Y ≤ Ltilde R e ⊔ centralizer (Z R e : Set (FreeAmalgam R)))
    (hcomm : ⁅Z R a,Y⁆ ≤ centralizer (Z R e : Set (FreeAmalgam R)))
    (hc : Y ≤ centralizer ((⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) : Set _)) :
    ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔ π.ker.map (U R e).subtype := by
  have hmove : ⁅Z R e,Y⁆ ≤ U R e :=
    commutator_le_moving_of_inner_mod_centralizer (Z R e) (Ltilde R e) Y
      ((map_subtype_le _).trans (Z_normalized R e)) hinner
  apply commutator_le_lifts_sup_kernel_of_fixed_section
    (Z R e) (U R e) (Z R a) Y (⁅Z R a,Z R e⁆)
    (critical_actor_normalizes_moving path) π
    (fun z v => Multiplicative.ofAdd (α z • v.toAdd)) hact
    {v | v.toAdd ∈ W} ?_ ?_ hmove hcomm ?_
  · intro v hv
    exact hfixed v.toAdd (fun z => congrArg Multiplicative.toAdd (hv z))
  · intro v hv
    obtain ⟨d,hd⟩ := hcover v.toAdd hv
    exact ⟨d,Multiplicative.toAdd.injective hd⟩
  · rwa [commutator_comm]
end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
