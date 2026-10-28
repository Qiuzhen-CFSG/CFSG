module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedKernel

/-!
# Exact kernel alternatives on the contained-image selected path

The original contained-image choices retain both individual whole-edge-Z
fixed equalities and every backward-path overlap. At each of these same
choices, missing the original Q-kernel is equivalent to strict growth
above the original mover image. If the kernel is contained, the images
have equal order and the whole X-layer has the source nonsplitting
property. At the minimal image order q², the selected original movers are
exactly the full kernel joined with the corresponding critical endpoint
conjugates.

These are the kernel and saturation clauses used in MS93 (5.5)(c),
(5.7)--(5.8), printed pp.915--920. They do not establish generation by
an unequal individual mover, the exceptional paired-mover generation,
the terminal exclusions, or the distance-two replacement witness.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same contained-image path carries the exact full-kernel alternatives
and, in the minimal-image branch, the literal endpoint saturation identities. -/
theorem Input.replacement_contained_large_kernel_backward_path
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype)
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₁)
        (Q d.radical c₁) (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
          Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₂)
        (Q d.radical c₂) (Q d.radical t₂) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
          Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ((Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
          (Q d.radical a) (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2 →
        J₁ = Q d.radical a ⊔ (Z d.radical z).map (MulAut.conj g).toMonoidHom ∧
        J₂ = Q d.radical a ⊔ ((Z d.radical z).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom) ∧
      (∀ v w : Vertex d.radical, (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) →
        let E := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical w) (Nat.card F^2)
        let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2)
        (¬ Q d.radical a ≤ E ∧ (Q d.radical a).relIndex J < (Q d.radical a).relIndex E) ∨
        (Q d.radical a ≤ E ∧ (Q d.radical a).relIndex E = (Q d.radical a).relIndex J ∧
          X d.radical a ≠ U d.radical a ⊔
            (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))) ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
          (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
        (∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) := by
  classical
  obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hgen₁,hgen₂,hfixed,hxn,hxp,he₁,he₂,hback⟩ :=
    h.replacement_contained_large_neighbor_fixed_backward_path d path hb hat hct hnormal
      B hB f hf hfQ hindex hlarge hcontained hJplane
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a = a := S.inv_mem hgS
  have hxa : act d.radical x a = a := hxS
  have transport (y : FreeAmalgam d.radical) (v w : Vertex d.radical) :
      Subgroup.SmallMover.join (U d.radical (act d.radical y v))
        (Q d.radical (act d.radical y v)) (Q d.radical (act d.radical y w)) (Nat.card F^2) =
      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2)).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]
  have hJ₁ : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) =
      J.map (MulAut.conj g).toMonoidHom := by
    simpa only [hga,inv_inv] using transport g⁻¹ a t
  have hJ₂ : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (act d.radical x (act d.radical g⁻¹ t))) (Nat.card F^2) =
      (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
    have hh := transport x a (act d.radical g⁻¹ t)
    rwa [hxa,hJ₁] at hh
  have hE₁ := transport g⁻¹ c t
  simp only [inv_inv] at hE₁
  change Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
    (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t))
      (Nat.card F^2) = E.map (MulAut.conj g).toMonoidHom at hE₁
  have hE₂ := transport x (act d.radical g⁻¹ c) (act d.radical g⁻¹ t)
  rw [hE₁] at hE₂
  refine ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hgen₁,hgen₂,hfixed,hxn,hxp,he₁,he₂,?_,?_,hback⟩
  · intro hJsmall
    obtain ⟨hsat,_⟩ := h.replacement_contained_minimal_endpoint_saturation d path hb hat hfirst
      B hB f hf hfQ hindex hlarge hcontained hJplane hJsmall
    have hQg : (Q d.radical a).map (MulAut.conj g).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hgS)
    have hQx : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a (S.inv_mem hxS))
    have hs₁ := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hsat
    change (Q d.radical a ⊔ Z d.radical z).map (MulAut.conj g).toMonoidHom =
      J.map (MulAut.conj g).toMonoidHom at hs₁
    rw [Subgroup.map_sup,hQg] at hs₁
    have hs₂ := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hs₁
    rw [Subgroup.map_sup,hQx] at hs₂
    exact ⟨hJ₁.trans hs₁.symm,hJ₂.trans hs₂.symm⟩
  · intro v w hvw
    have hne₁ : Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
        (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t))
          (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) := by
      rw [hE₁,hJ₁]
      exact fun hh => hne (Subgroup.map_injective (MulAut.conj g).injective hh)
    have hne₂ : Subgroup.SmallMover.join
        (U d.radical (act d.radical x (act d.radical g⁻¹ c)))
        (Q d.radical (act d.radical x (act d.radical g⁻¹ c)))
        (Q d.radical (act d.radical x (act d.radical g⁻¹ t))) (Nat.card F^2) ≠
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (act d.radical x (act d.radical g⁻¹ t))) (Nat.card F^2) := by
      rw [hE₂,hJ₂]
      intro hh
      exact hne (Subgroup.map_injective (MulAut.conj g).injective
        (Subgroup.map_injective (MulAut.conj x⁻¹).injective hh))
    have haw : Adjacent d.radical a w := by
      rcases hvw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    have hvw' : Adjacent d.radical v w := by
      rcases hvw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    have hne' : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
          (Q d.radical a) (Q d.radical w) (Nat.card F^2) := by
      rcases hvw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    obtain ⟨heq,hlt⟩ := h.replacement_neighbor_kernel_iff_image_eq d path.start_color haw hvw'
    by_cases hQE : Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical v)
        (Q d.radical v) (Q d.radical w) (Nat.card F^2)
    · exact Or.inr ⟨hQE,heq.mp hQE,h.replacement_unequal_kernel_nonsplitting d geometry hb
        path.start_color haw hvw' hne' hQE⟩
    · exact Or.inl ⟨hQE,hlt.mp hQE⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
