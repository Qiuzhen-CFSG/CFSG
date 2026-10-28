module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage.InitialCover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover.Ambient
public import Theory.Representation.SymplecticFourOrthogonalCover.MovingIndex

/-!
# The faithful whole-vertex action on the initial natural quotient

The same marked moved cover used at every original-color vertex carries the
entire ambient quotient action. Its component restriction is the literal
natural symplectic action; the trivial component centralizer makes the full
action faithful. Original vertex coordinates transport the quotient map with
mapped kernel exactly Q=C(Z), preserve the residual image, and intertwine the
projection with the actual conjugation action on the embedded moving layer.

Source: MS93 (3.2)(vi) and (3.3), pp.866–867. These data support the critical
plane comparison before the later whole-quotient outer-removal conclusion.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- Original vertex coordinates retain both the moving layer and the exact core. -/
theorem vertex_coordinates_with_kernel (R : Subgroup H)
    (hp : IsPGroup 2 R) (hQR : pCore 2 H ≤ R)
    {a : Vertex R} (ha : color R a = false) :
    ∃ i : H →* FreeAmalgam R, Function.Injective i ∧
      i.range = stabilizer R a ∧ (pResidual 2 H).map i = Ltilde R a ∧
      (LocalPackage.initialLayer R).map i = U R a ∧
      (pCore 2 H).map i = Q R a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_,?_⟩
  · have h := stabilizer_act R g (alpha R)
    dsimp only [i]
    rw [MonoidHom.range_comp]
    change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom = _
    simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using h.symm
  · have h := Ltilde_act R g (alpha R)
    rw [Ltilde_alpha] at h
    simpa only [alpha,act_mVertex,one_mul,map_map] using h.symm
  · have h := U_act R g (alpha R)
    rw [←LocalPackage.initialLayer_map R] at h
    simpa only [alpha,act_mVertex,one_mul,map_map] using h.symm
  · have h := Q_act R g (alpha R)
    rw [Q_alpha R hp hQR] at h
    simpa only [alpha,act_mVertex,one_mul,map_map] using h.symm

/-- The natural coordinates of the actual moved section extend to the whole
vertex quotient with kernel exactly its Z-centralizer. The same projection
and embedding retain the original full ambient conjugation action. -/
theorem ambient_initial_cover_at_vertex
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {a : Vertex R} (ha : color R a = false) :
    letI : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
    let ρ := NormalElementaryQuotient.representation (omegaCenterIn (pCore 2 H)) q hq
      (hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm)
    let s := MovedSection.ofNormal ρ ((pResidual 2 H).map q)
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ e : ActionEquiv (s.action.comp ((pResidual 2 H).map q).subtype)
          (binaryNatural (K := F.Carrier)), IsCover (MovedSection.coverProjection s e) ∧
      ∃ j : Multiplicative s.space.toSubmodule →* FreeAmalgam R,
        Function.Injective j ∧ j.range = U R a ∧
      ∃ κ : stabilizer R a →* J, Function.Surjective κ ∧
        κ.ker.map (stabilizer R a).subtype = Q R a ∧
        κ.ker.map (stabilizer R a).subtype = C R a ∧
        ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = (pResidual 2 H).map q ∧
        Function.Injective (MovedSection.ambientAction s e) ∧
        (∀ (g : stabilizer R a) (v : s.space.toSubmodule),
          j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
            (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹) ∧
        (∀ (g : stabilizer R a) (v : s.space.toSubmodule),
          MovedSection.coverProjection s e (s.space.toRepresentation (κ g) v) =
            MovedSection.ambientAction s e (κ g) (MovedSection.coverProjection s e v)) ∧
        (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
          j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  dsimp only
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he⟩ := centralOmega_initial_cover R hms hp hne hQR hself hfaith
    q hq hcore ((pResidual 2 H).map q) hc hC hsq
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel R hp hQR ha
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 H))
    (pResidual 2 H) q hq hk)
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer R a) hir
  have hkQ : κ.ker.map (stabilizer R a).subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel, hcore]
    exact hiQ
  refine ⟨F,hF,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),?_,
    κ,ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq,hkQ,?_,?_,
    MovedSection.ambientAction_faithful s e binaryNatural_injective hC,?_,?_,?_⟩
  · dsimp only [j]
    rw [MonoidHom.range_comp, ElementaryMovedCover.embedding_range,
      ← initialCore_eq R hms hp hne hQR hself hfaith q hq hcore
        (pResidual 2 H) ((pResidual 2 H).map q) rfl hc hC hsq]
    exact hiU
  · exact hkQ.trans (MSCentralOrbit.C_eq_Q R hp hQR hfaith a ha).symm
  · rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  · exact ElementaryMovedCover.embedded_ambient_conjugate _ _ _ _ _ i hi _ hir
  · intro g v
    exact MovedSection.coverProjection_ambient s e (κ g) v
  · obtain ⟨f,hf,hact,hker⟩ := ElementaryMovedCover.exists_conjugationActor
      (omegaCenterIn (pCore 2 H)) (pResidual 2 H) q hq hk i hi (Ltilde R a) hiL e
    exact hker

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
