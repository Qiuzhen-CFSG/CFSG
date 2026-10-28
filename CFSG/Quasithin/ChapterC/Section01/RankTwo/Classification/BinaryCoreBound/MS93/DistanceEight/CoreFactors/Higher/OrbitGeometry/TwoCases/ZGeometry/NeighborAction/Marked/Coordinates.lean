module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Transport

/-!
# Compatible coordinates at the neighboring center

One actual conjugator transports the source local group and its natural
coordinates. Pulling both higher layers back by the inverse conjugator then
transports the supplied doubled-dual section through the same marking.
The formulas retain both later vertices of the second orbit layer.

Source: Meierfrankenfeld--Stellmacher (1993), notation p.881 and
(4.5.4)(iii), pp.898--899. The marked section remains an explicit input;
its construction belongs to the higher marked-quotient source producer.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked
open DistanceFour.Linear ModuleAlternatives.SourceCalculation NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry) {c : Vertex R}
  (g : FreeAmalgam R) (hg : act R g (alpha R) = c)

/-- The actual local identification, with the specified conjugator. -/
noncomputable def localEquiv : M ≃* stabilizer R c :=
  (Frame.mk g hg).localEquiv

@[simp] theorem localEquiv_val (m : M) :
    (localEquiv g hg m : FreeAmalgam R) = g⁻¹ * embedM R m * g := by
  simp only [localEquiv, Frame.localEquiv_val, Frame.conjugation, MulAut.conj_apply, inv_inv]

/-- The marked source projection in the transported chart. -/
noncomputable def projection : stabilizer R c →* S :=
  common.natural.marking.toMonoidHom.comp
    (source.projection.comp (localEquiv g hg).symm.toMonoidHom)

@[simp] theorem projection_localEquiv (m : M) :
    projection common g hg (localEquiv g hg m) =
      common.natural.marking (source.projection m) := by
  simp [projection]

theorem projection_onto : Function.Surjective (projection common g hg) :=
  common.natural.marking.surjective.comp
    (source.projection_surjective.comp (localEquiv g hg).symm.surjective)

theorem projection_kernel [Finite M] :
    (projection common g hg).ker = (Q R c).subgroupOf (stabilizer R c) := by
  have he : (projection common g hg).ker = ((Frame.mk g hg).projection source).ker := by
    ext x
    change common.natural.marking _ = 1 ↔ _ = 1
    exact common.natural.marking.map_eq_one_iff
  rw [he]
  exact (Frame.mk g hg).projection_kernel source

/-- Natural coordinates use precisely CommonFacts.natural and its marking. -/
noncomputable def naturalEquiv : U R c ≃* Multiplicative W :=
  (Frame.mk g hg).movingEquiv.symm.trans common.natural.equiv

theorem natural_action (q : stabilizer R c) (u v : U R c)
    (hv : (v : FreeAmalgam R) = (q : FreeAmalgam R) *
      (u : FreeAmalgam R) * (q : FreeAmalgam R)⁻¹) :
    (naturalEquiv common g hg v).toAdd =
      (projection common g hg q).val.mulVec (naturalEquiv common g hg u).toAdd := by
  exact ((Frame.mk g hg).natural common.natural).action q u v hv

/-- Literal pullback of a subgroup by the inverse of the chart conjugator. -/
noncomputable def pullback (A : Subgroup (FreeAmalgam R)) :
    A ≃* rightConjugate A g⁻¹ :=
  (MulAut.conj g⁻¹⁻¹).subgroupMap A

@[simp] theorem pullback_val (A : Subgroup (FreeAmalgam R)) (x : A) :
    (pullback g A x : FreeAmalgam R) = g * (x : FreeAmalgam R) * g⁻¹ := by
  change g⁻¹⁻¹ * (x : FreeAmalgam R) * (g⁻¹⁻¹)⁻¹ = _
  simp only [inv_inv]

private theorem pullback_conjugate (A : Subgroup (FreeAmalgam R))
    (m : M) (x y : A)
    (hy : (y : FreeAmalgam R) = (localEquiv g hg m : FreeAmalgam R) *
      (x : FreeAmalgam R) * (localEquiv g hg m : FreeAmalgam R)⁻¹) :
    (pullback g A y : FreeAmalgam R) = embedM R m *
      (pullback g A x : FreeAmalgam R) * (embedM R m)⁻¹ := by
  rw [pullback_val, pullback_val, hy, localEquiv_val]
  group

variable {common g hg}

/-- The supplied quotient transported back to the actual neighboring layer. -/
noncomputable def pairQuotient {A B : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common
      (rightConjugate A g⁻¹) (rightConjugate B g⁻¹) true) :
    A →* Multiplicative (W × W) :=
  s.quotient.comp (pullback g A).toMonoidHom

theorem pairQuotient_onto {A B : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common
      (rightConjugate A g⁻¹) (rightConjugate B g⁻¹) true) :
    Function.Surjective (pairQuotient s) := s.onto.comp (pullback g A).surjective

theorem pairQuotient_kernel {A B : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common
      (rightConjugate A g⁻¹) (rightConjugate B g⁻¹) true) :
    (pairQuotient s).ker = B.subgroupOf A := by
  ext x
  change s.quotient (pullback g A x) = 1 ↔ (x : FreeAmalgam R) ∈ B
  change pullback g A x ∈ s.quotient.ker ↔ _
  rw [s.kernel]
  change (MulAut.conj g⁻¹⁻¹).toMonoidHom (x : FreeAmalgam R) ∈
    B.map (MulAut.conj g⁻¹⁻¹).toMonoidHom ↔ _
  exact mem_map_iff_mem (MulAut.conj g⁻¹⁻¹).injective

theorem pairQuotient_action {A B : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common
      (rightConjugate A g⁻¹) (rightConjugate B g⁻¹) true)
    (hg : act R g (alpha R) = c) (q : stabilizer R c) (x y : A)
    (hy : (y : FreeAmalgam R) = (q : FreeAmalgam R) *
      (x : FreeAmalgam R) * (q : FreeAmalgam R)⁻¹) :
    (pairQuotient s y).toAdd =
      (dual (projection common g hg q) (pairQuotient s x).toAdd.1,
       dual (projection common g hg q) (pairQuotient s x).toAdd.2) := by
  obtain ⟨m, rfl⟩ := (localEquiv g hg).surjective q
  simpa only [pairQuotient, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    projection_localEquiv, Bool.true_eq, reduceIte] using
    s.action m (pullback g A x) (pullback g A y) (pullback_conjugate g hg A m x y hy)

/-- Pullback retains both actual forward vertices. -/
theorem pulled_second {d e : Vertex R} (hg : act R g (alpha R) = c) :
    rightConjugate (hatW R c d e) g⁻¹ =
      hatW R (alpha R) (act R g⁻¹ d) (act R g⁻¹ e) := by
  rw [rightConjugate_hatW, ← hg, ← act_mul, mul_inv_cancel, act_one]

/-- The denominator uses the same pulled forward vertex as the numerator. -/
theorem pulled_first {d : Vertex R} (hg : act R g (alpha R) = c) :
    rightConjugate (hatV R c d) g⁻¹ = hatV R (alpha R) (act R g⁻¹ d) := by
  rw [rightConjugate_hatV, ← hg, ← act_mul, mul_inv_cancel, act_one]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked
