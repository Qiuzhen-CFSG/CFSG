module
public import Theory.Representation.G2BinaryParabolicFrame
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry
/-!
# The pointwise stabilizer of the marked binary plane

A fixed natural coordinate vector lifts uniquely to its singular octonion
basis vector: trace identifies the two diagonal coordinates and norm makes
them zero. Fixing both plane generators therefore puts the actor in both
geometric parabolics. Their intersection is the Borel, which is the actual
unipotent two-group over F₂. The marked cubic moves a plane generator.

Application: the plane residual's literal action kernel in 13.3.15 and
13.3.18 is a two-group; source printed pp.894–895.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.SplitOctonion Atlas.G2.LieParabolicSetup

private theorem fixes_basis_lift (g:Model F) (i:Fin 2)
    (h:Restricted.NaturalCoordinates.action F g (Pi.single (i.castLE (by decide)) 1)=
      Pi.single (i.castLE (by decide)) 1) :
    g.val (basisVector (i.castLE (by decide)))=basisVector (i.castLE (by decide)) := by
  let b:Carrier F:=basisVector (i.castLE (by decide))
  have hr:(representative F (Pi.single (i.castLE (by decide)) 1)).val=b := by
    ext j;fin_cases i <;>fin_cases j <;>simp [representative,b,basisVector]
  rw [action_apply] at h
  change ![g.val ((representative F _).val) 0,g.val ((representative F _).val) 1,
    g.val ((representative F _).val) 2,g.val ((representative F _).val) 5,
    g.val ((representative F _).val) 6,g.val ((representative F _).val) 7]=_ at h
  rw [hr] at h
  have h0:=congrFun h 0
  have h1:=congrFun h 1
  have h2:=congrFun h 2
  have h5:=congrFun h 3
  have h6:=congrFun h 4
  have h7:=congrFun h 5
  have ht:trace (g.val b)=0 := by
    rw [automorphism_trace]
    fin_cases i <;>simp [b,trace,basisVector]
  have hn:Atlas.SplitOctonion.norm (g.val b)=0 := by
    rw [automorphism_norm]
    fin_cases i <;>simp [b,Atlas.SplitOctonion.norm,basisVector]
  have hd:g.val b 3=g.val b 4 := by
    exact (eq_neg_of_add_eq_zero_left ht).trans (CharTwo.neg_eq _)
  have hz:g.val b 4=0 := by
    apply mul_self_eq_zero.mp
    fin_cases i <;>simp_all [Atlas.SplitOctonion.norm]
  change g.val b=b
  ext j;fin_cases i <;>fin_cases j <;>simp_all [b,basisVector]

/-- Fixing the first natural coordinate vector gives the original point parabolic. -/
theorem fixes_first_mem_parabolic (g:Model F)
    (h:Restricted.NaturalCoordinates.action F g (Pi.single 0 1)=Pi.single 0 1) : g∈parabolic :=
  fixingFirstVector_le_parabolic (fixes_basis_lift g 0 h)

/-- Fixing the two literal plane generators places an actor in the actual
binary Borel, hence in the original unipotent two-group. -/
theorem plane_pointwise_le_unipotent (g:Model F)
    (hg:∀v∈plane,Restricted.NaturalCoordinates.action F g v=v) : g∈unipotent := by
  have hf (i:Fin 2):g.val (basisVector (i.castLE (by decide)))=basisVector (i.castLE (by decide)) :=
    fixes_basis_lift g i (hg _ (by rw [mem_plane];fin_cases i <;>simp))
  have hfix (x:Carrier F) (hx:x∈shortPlane):g.val x=x := by
    have he:x=x 0•basisVector 0+x 1•basisVector 1 := by
      ext j;fin_cases j <;>simp [basisVector,hx 2 (by decide),hx 3 (by decide),
        hx 4 (by decide),hx 5 (by decide),hx 6 (by decide),hx 7 (by decide)]
    have h0:g.val (basisVector 0)=basisVector 0:=hf 0
    have h1:g.val (basisVector 1)=basisVector 1:=hf 1
    calc
      g.val x=g.val (x 0•basisVector 0+x 1•basisVector 1):=congrArg g.val he
      _=x 0•basisVector 0+x 1•basisVector 1:=by rw [map_add,map_smul,map_smul,h0,h1]
      _=x:=he.symm
  have hp:g∈shortPlaneStabilizer := by
    constructor
    · intro x hx;rw [hfix x hx];exact hx
    · intro x hx
      have hi:g.val.symm x=x := by
        apply g.val.injective
        change g.val (g.val.symm x)=g.val x
        rw [hfix x hx]
        exact g.val.apply_symm_apply x
      rw [hi];exact hx
  have hb:g∈borel := shortPlaneStabilizer_inf_parabolic₂.le
    ⟨hp,fixingFirstVector_le_parabolic (hf 0)⟩
  rwa [borel_eq_unipotent_of_card_two (by simp [Nat.card_eq_fintype_card])] at hb

theorem plane_cubic_moves :
    Restricted.NaturalCoordinates.action F BinaryParabolicPair.cubicActor (Pi.single 0 1)≠Pi.single 0 1 := by
  intro he
  have hh:=congrFun he 1
  simp [BinaryParabolicPair.cubicActor,BinaryParabolicPair.shortRoot,map_mul,Module.End.mul_apply] at hh
end Atlas.G2.Natural.BinaryPointFlag
