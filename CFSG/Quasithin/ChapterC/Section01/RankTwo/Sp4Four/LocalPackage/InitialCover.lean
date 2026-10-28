module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.InitialCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerCover
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover.Transport

/-!
# The initial natural cover at every Sp4(4) graph vertex

The initial central omega commutator equals the Sylow-center orbit
commutator. Injective amalgam coordinates identify this group with the
literal graph subgroup U at each M-vertex. Transport of the marked cover
then gives the actual conjugation action of the vertex residual and the
projection kernel given by its centralizer in U. Central fixed extensions
are retained. No later intrinsic-core reconstruction is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (3.2)(vi), (1.5)(ii).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem vertex_coordinates (R : Subgroup H)
    {a : Vertex R} (ha : color R a = false) :
    ∃ i : H →* FreeAmalgam R, Function.Injective i ∧
      i.range = stabilizer R a ∧ (pResidual 2 H).map i = Ltilde R a ∧
      (initialLayer R).map i = U R a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_⟩
  · have h := stabilizer_act R g (alpha R)
    dsimp only [i]
    rw [MonoidHom.range_comp]
    change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom = _
    simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using h.symm
  · have h := Ltilde_act R g (alpha R)
    rw [Ltilde_alpha] at h
    simpa only [alpha,act_mVertex,one_mul,map_map] using h.symm
  · have h := U_act R g (alpha R)
    rw [←initialLayer_map R] at h
    simpa only [alpha,act_mVertex,one_mul,map_map] using h.symm

/-- The cover of the literal graph layer, with its actual conjugation actor. -/
theorem initial_cover_at_vertex
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
    letI : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) :=
      omegaCenterIn_elementary _
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) q hq
      (hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm)
    let s := MovedSection.ofNormal ρ ((pResidual 2 H).map q)
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ e : ActionEquiv (s.action.comp ((pResidual 2 H).map q).subtype)
          (binaryNatural (K := F.Carrier)),
        IsCover (MovedSection.coverProjection s e) ∧
        ∃ j : Multiplicative s.space.toSubmodule →* FreeAmalgam R,
          Function.Injective j ∧ j.range = U R a ∧
          ∃ f : Ltilde R a →* commutator (Matrix.symplecticGroup (Fin 2) F.Carrier),
            Function.Surjective f ∧
            (∀ (k : Ltilde R a) (v : s.space.toSubmodule),
              j (Multiplicative.ofAdd (MovedSection.coverAction s e (f k) v)) =
                (k:FreeAmalgam R) * j (Multiplicative.ofAdd v) * (k:FreeAmalgam R)⁻¹) ∧
            (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
              j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  dsimp only
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he⟩ := centralOmega_initial_cover R hms hp hne hQR hself hfaith
    q hq hcore ((pResidual 2 H).map q) hc hC hsq
  obtain ⟨i,hi,hir,hiL,hiU⟩ := vertex_coordinates R ha
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 H))
    (pResidual 2 H) q hq hk)
  refine ⟨F,hF,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),?_,?_⟩
  · dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,
      ←initialCore_eq R hms hp hne hQR hself hfaith q hq hcore
        (pResidual 2 H) ((pResidual 2 H).map q) rfl hc hC hsq]
    exact hiU
  · exact ElementaryMovedCover.exists_conjugationActor (omegaCenterIn (pCore 2 H))
      (pResidual 2 H) q hq hk i hi (Ltilde R a) hiL e
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
