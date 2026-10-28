module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitTerminal
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitFixedDisplacement
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
/-!
# Natural-quotient assembly for the actual critical orbit

A natural quotient of the literal orbit representation, with its possibly
outer S6 marking, gives the actual A/D conjugation section. The component
fixed-space equality identifies its kernel exactly. Surjectivity of the
original projection supplies nonzero-vector transitivity after the marking.
The linear fixed-kernel displacement bound then invokes the already proved
paired-orbit contradiction. Every subgroup, coordinate map and free-amalgam
embedding remains the one supplied by the native source.

The remaining linear inputs are precisely the natural quotient and
augmentation-cover recognition outputs for this action.
Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem false_of_criticalOrbit_natural_quotient
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hnB : stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)))
    (helem : IsElementaryAbelian 2 (criticalOrbit R c b ⊓ B : Subgroup (FreeAmalgam R)))
    [IsElementaryAbelian 2 (OrbitQuotient R c b)]
    (hsurj : Function.Surjective s.projection)
    (e : S ≃* S)
    (p : Additive (OrbitQuotient R c b) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hp : Function.Surjective p)
    (hk : p.ker = fixedSpace (s.orbitFullRepresentation hb hc hab hcb hsurj)
      (alternatingGroup (Fin 6)))
    (he : ∀ g v, p (s.orbitFullRepresentation hb hc hab hcb hsurj g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (e g) (p v))
    (hfix : fixedSpace (s.orbitFullRepresentation hb hc hab hcb hsurj) (alternatingGroup (Fin 6)) ≤
      subspaceCommutator (s.orbitFullRepresentation hb hc hab hcb hsurj) ⊤ (s.orbitActorImage B)) : False := by
  let σ := (BinaryPermutation.naturalRepresentation (Fin 6)).comp
    (e.toMonoidHom.comp (s.projection.comp (⊤ : Subgroup M).subtype))
  let f : (orbitRepresentation R c b).IntertwiningMap σ := {
    toLinearMap := p
    isIntertwining' := fun m => by
      apply LinearMap.ext
      intro v
      change p (orbitRepresentation R c b m v) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e (s.projection m)) (p v)
      rw [←s.orbitFullRepresentation_projection hb hc hab hcb hsurj m]
      exact he (s.projection m) v }
  have hk0 : p.ker = orbitFixedSpace L R c b := by
    rw [hk]
    ext v
    constructor
    · intro hv l
      change orbitRepresentation R c b ⟨l,mem_top _⟩ v = v
      rw [←s.orbitFullRepresentation_projection hb hc hab hcb hsurj]
      exact hv ⟨s.projection l,s.component_image ▸ mem_map_of_mem s.projection l.property⟩
    · intro hv g
      obtain ⟨l,hl,heq⟩ := s.component_image.ge g.property
      change s.orbitFullRepresentation hb hc hab hcb hsurj g.val v = v
      rw [←heq,s.orbitFullRepresentation_projection hb hc hab hcb hsurj ⟨l,mem_top _⟩]
      exact hv ⟨l,hl⟩
  let d := orbitFixedSection L R c b (s.orbitLayer_le_orbit hb hc hab hcb) f hp hk0
  have htrans : ∀ u v : BinaryPermutation.natural (Fin 6), u ≠ 0 → v ≠ 0 →
      ∃ m : (⊤ : Subgroup M), σ m u = v := by
    intro u v hu hv
    obtain ⟨g,hg⟩ := NaturalTransport.transitive_nonzero u v hu hv
    obtain ⟨m,hm⟩ := hsurj (e.symm g.val)
    refine ⟨⟨m,mem_top _⟩,?_⟩
    change BinaryPermutation.naturalRepresentation (Fin 6) (e (s.projection m)) u = v
    rw [hm,e.apply_symm_apply]
    exact hg
  exact s.false_of_criticalOrbit_paired_section h t hfull hb hlarge hc hab hcb himage B hBQ hnB
    helem (s.orbitFixedKernel_le_commutator_sup_of_linear_bound hb hc hab hcb hsurj B hBQ hfix) d htrans
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
