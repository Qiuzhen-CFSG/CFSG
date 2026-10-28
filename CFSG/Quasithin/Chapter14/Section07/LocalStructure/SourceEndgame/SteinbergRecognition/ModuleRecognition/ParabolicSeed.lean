module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.Contracts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.SourceMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.Quotient

/-!
# Assembly of the marked parabolic seed on the original quotient

A compatible point/line marking and transitivity on the three nonzero vectors
of the original U/V plane suffice to construct the H.6.5 seed. The Borel is a
two-group, so it fixes a nonzero plane vector. Local transitivity makes its
line-parabolic orbit span the plane; the original conjugate-span definition
then makes its full orbit generate S/V. H.6.5 gives all five actual alternatives.
The residual actor identity follows functorially from the same marking.

The marking and the local transitivity are separate, explicit mathematical
obligations. This conditional assembly does not assert the source theorem
until their producers have discharged them. No cyclic vector or orbit
dimension is an input to the construction below.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
using H.6.5, printed p.388 (PDF p.399), manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
open Chapter12.Section08 CriticalFusion.Source BinaryLinearThree.ParabolicCyclic
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

variable [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- Transitivity on the nonzero plane vectors proves irreducibility for
exactly the original residual actor, expressed through its invariant subspaces. -/
theorem LocalTransitive.irreducible (a : QuotientAction d)
    (hlocal : LocalTransitive d a)
    (A : Submodule (ZMod 2) (Additive (S F L ⧸ V.subgroupOf (S F L))))
    (hA : A ≤ plane (F := F) (L := L) (V := V))
    (hstable : ∀ l : L, (l : G) ∈ F.Li L 1 → ∀ v ∈ A,
      a.representation (d.qL l) v ∈ A) :
    A = ⊥ ∨ A = plane (F := F) (L := L) (V := V) := by
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  apply le_antisymm hA
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0]; exact A.zero_mem
  obtain ⟨l, hl, he⟩ := hlocal m v (hA hm) hv hm0 hv0
  exact he ▸ hstable l hl m hm

/-- The chosen line parabolic preserves precisely the original U/V plane. -/
theorem Marking.plane_stable (b : Marking d) (a : QuotientAction d)
    (g : BinaryLinearThree.Group) (hg : g ∈ Matrix.PSL3Two.lineParabolicSL)
    (v : Additive (S F L ⧸ V.subgroupOf (S F L)))
    (hv : v ∈ plane (F := F) (L := L) (V := V)) :
    (a.representation.comp b.twist.toMonoidHom) g v ∈
      plane (F := F) (L := L) (V := V) := by
  rw [← b.parabolic] at hg
  obtain ⟨l, hl, he⟩ := hg
  have hq : d.qL l = b.twist g := by
    apply b.twist.symm.injective
    exact he.trans (b.twist.symm_apply_apply g).symm
  change a.representation (b.twist g) v ∈ _
  rw [← hq]
  exact ParabolicSeed.plane_stable d a l hl v hv

/-- The Borel fixes a nonzero vector of the actual plane. -/
theorem Marking.exists_fixed_plane_vector (b : Marking d) (a : QuotientAction d)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) :
    ∃ m : Additive (S F L ⧸ V.subgroupOf (S F L)),
      m ∈ plane (F := F) (L := L) (V := V) ∧ m ≠ 0 ∧
      ∀ g ∈ Matrix.PSL3Two.borelSL, (a.representation.comp b.twist.toMonoidHom) g m = m := by
  let D := plane (F := F) (L := L) (V := V)
  let ρ := a.representation.comp b.twist.toMonoidHom
  have hBL : Matrix.PSL3Two.borelSL ≤ Matrix.PSL3Two.lineParabolicSL := inf_le_right
  let : MulAction Matrix.PSL3Two.borelSL D := {
    smul g v := ⟨ρ g v, b.plane_stable d a g (hBL g.property) v v.property⟩
    one_smul v := by apply Subtype.ext; exact congrArg (fun f => f v.val) ρ.map_one
    mul_smul g h v := by apply Subtype.ext; exact congrArg (fun f => f v.val) (ρ.map_mul g h) }
  have hB : IsPGroup 2 Matrix.PSL3Two.borelSL :=
    IsPGroup.of_card (n := 3) Matrix.PSL3Two.card_borelSL
  have hcard : 2 ∣ Nat.card D := by rw [card_plane d hs hU₀]; decide
  obtain ⟨v, hv, hn⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := D) hcard (show (0 : D) ∈ MulAction.fixedPoints Matrix.PSL3Two.borelSL D by
      intro g; apply Subtype.ext; exact map_zero (ρ g))
  refine ⟨v, v.property, fun hz => hn (Subtype.ext hz.symm), ?_⟩
  intro g hg
  exact congrArg Subtype.val (hv ⟨g, hg⟩)

/-- Local transitivity identifies the whole line-parabolic orbit span,
rather than assuming its dimension. -/
theorem Marking.line_orbitSpan (b : Marking d) (a : QuotientAction d)
    (hlocal : LocalTransitive d a)
    (m : Additive (S F L ⧸ V.subgroupOf (S F L)))
    (hm : m ∈ plane (F := F) (L := L) (V := V)) (hm0 : m ≠ 0) :
    orbitSpan (a.representation.comp b.twist.toMonoidHom)
      Matrix.PSL3Two.lineParabolicSL m = plane (F := F) (L := L) (V := V) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨g, hg, rfl⟩
    exact b.plane_stable d a g hg m hm
  · intro v hv
    by_cases hz : v = 0
    · rw [hz]; exact Submodule.zero_mem _
    obtain ⟨l, hl, he⟩ := hlocal m v hm hv hm0 hz
    have hg : b.twist.symm (d.qL l) ∈ Matrix.PSL3Two.lineParabolicSL := by
      rw [← b.parabolic]
      exact ⟨l, (F.Li_le L 1 hl).2, rfl⟩
    have hmem := orbit_mem (a.representation.comp b.twist.toMonoidHom)
      Matrix.PSL3Two.lineParabolicSL m _ hg
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, he] using hmem

/-- The original conjugate-span construction makes that same vector cyclic. -/
theorem Marking.full_orbitSpan (b : Marking d) (a : QuotientAction d)
    (hlocal : LocalTransitive d a)
    (m : Additive (S F L ⧸ V.subgroupOf (S F L)))
    (hm : m ∈ plane (F := F) (L := L) (V := V)) (hm0 : m ≠ 0) :
    orbitSpan (a.representation.comp b.twist.toMonoidHom) ⊤ m = ⊤ := by
  let A := orbitSpan (a.representation.comp b.twist.toMonoidHom) ⊤ m
  apply eq_top_of_plane_le d a A
  · rw [← b.line_orbitSpan d a hlocal m hm hm0]
    apply Submodule.span_mono
    rintro v ⟨g, _, he⟩
    exact ⟨g, mem_top g, he⟩
  · intro g v hv
    have h := orbitSpan_stable (a.representation.comp b.twist.toMonoidHom)
      ⊤ m (b.twist.symm g) (mem_top _) v hv
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using h

/-- The seed is an actual U-element modulo V, fixed by the marked Borel,
cyclic under L, with its line-parabolic orbit spanning a plane. -/
theorem exists_seed_of_local_transitive (b : Marking d) (a : QuotientAction d)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) (hlocal : LocalTransitive d a) :
    ∃ s : S F L, (s : G) ∈ F.U ∧ (s : G) ∉ V ∧
      (∀ g ∈ Matrix.PSL3Two.borelSL, (a.representation.comp b.twist.toMonoidHom) g
        (quotientCoordinates s).toAdd = (quotientCoordinates s).toAdd) ∧
      orbitSpan (a.representation.comp b.twist.toMonoidHom) ⊤
        (quotientCoordinates s).toAdd = ⊤ ∧
      Module.finrank (ZMod 2) (orbitSpan (a.representation.comp b.twist.toMonoidHom)
        Matrix.PSL3Two.lineParabolicSL (quotientCoordinates s).toAdd) = 2 := by
  obtain ⟨m, hm, hm0, hfix⟩ := b.exists_fixed_plane_vector d a hs hU₀
  obtain ⟨s, hsU, rfl⟩ := (mem_plane_iff m).mp hm
  refine ⟨s, hsU, ?_, hfix, b.full_orbitSpan d a hlocal _ hm hm0, ?_⟩
  · intro hsV
    exact hm0 ((QuotientGroup.eq_one_iff s).mpr hsV)
  · rw [b.line_orbitSpan d a hlocal _ hm hm0]
    exact finrank_plane d hs hU₀

/-- The actual five H.6.5 alternatives for this twist of the literal S/V action.
The marking and original-plane transitivity still require source proofs. -/
theorem alternatives_of_local_transitive (b : Marking d) (a : QuotientAction d)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) (hlocal : LocalTransitive d a) :
    Alternatives (a.representation.comp b.twist.toMonoidHom) := by
  obtain ⟨s, _, _, hfix, hgen, hdim⟩ := exists_seed_of_local_transitive d b a hs hU₀ hlocal
  exact parabolic_seed_alternatives _ (quotientCoordinates s).toAdd hfix hgen hdim

omit [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))] in
/-- The source generation inputs construct the actual quotient action, its
compatible point/line marking, and the literal cyclic parabolic seed.

The normality and elementary-abelian instances are supplied by the generation
conclusion `hPhi`; the actor is the representation descended through the
original `d.qL`.  Thus the returned seed is the one on `S/V`, with no
containment of `S` in `L` and no recognition conclusion built into the
interface. -/
theorem exists_source_seed_of_generation
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hSQ : S F L ≤ Q T L)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hcomm : ⁅S F L, Q T L⁆ ≤ V)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) :
    letI : (V.subgroupOf (S F L)).Normal :=
      quotient_normal (F := F) (L := L) (V := V) hPhi
    letI : IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L)) :=
      quotient_elementary (F := F) (L := L) (V := V) hSQ hPhi
    ∃ a : QuotientAction d, ∃ b : Marking d, ∃ s : S F L,
      (s : G) ∈ F.U ∧ (s : G) ∉ V ∧
      (∀ g ∈ Matrix.PSL3Two.borelSL,
        (a.representation.comp b.twist.toMonoidHom) g
          (quotientCoordinates s).toAdd = (quotientCoordinates s).toAdd) ∧
      orbitSpan (a.representation.comp b.twist.toMonoidHom) ⊤
          (quotientCoordinates s).toAdd = ⊤ ∧
      Module.finrank (ZMod 2)
          (orbitSpan (a.representation.comp b.twist.toMonoidHom)
            Matrix.PSL3Two.lineParabolicSL (quotientCoordinates s).toAdd) = 2 := by
  let _ : (V.subgroupOf (S F L)).Normal :=
    quotient_normal (F := F) (L := L) (V := V) hPhi
  let _ : IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L)) :=
    quotient_elementary (F := F) (L := L) (V := V) hSQ hPhi
  let a : QuotientAction d := quotientAction d hTL hcomm
  obtain ⟨b⟩ := nonempty_marking d hTL
  have hlocal : LocalTransitive d a :=
    LocalAction.localTransitive d a hs hU₀ hTL
  obtain ⟨s, hsU, hsV, hfix, hgen, hdim⟩ :=
    exists_seed_of_local_transitive d b a hs hU₀ hlocal
  exact ⟨a, b, s, hsU, hsV, hfix, hgen, hdim⟩

omit [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))] in
/-- The same source assembly, with H.6.5's five alternatives exposed for the
literal quotient representation. -/
theorem source_alternatives_of_generation
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hSQ : S F L ≤ Q T L)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hcomm : ⁅S F L, Q T L⁆ ≤ V)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) :
    letI : (V.subgroupOf (S F L)).Normal :=
      quotient_normal (F := F) (L := L) (V := V) hPhi
    letI : IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L)) :=
      quotient_elementary (F := F) (L := L) (V := V) hSQ hPhi
    ∃ a : QuotientAction d, ∃ b : Marking d,
      Alternatives (a.representation.comp b.twist.toMonoidHom) := by
  let _ : (V.subgroupOf (S F L)).Normal :=
    quotient_normal (F := F) (L := L) (V := V) hPhi
  let _ : IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L)) :=
    quotient_elementary (F := F) (L := L) (V := V) hSQ hPhi
  let a : QuotientAction d := quotientAction d hTL hcomm
  obtain ⟨b⟩ := nonempty_marking d hTL
  have hlocal : LocalTransitive d a :=
    LocalAction.localTransitive d a hs hU₀ hTL
  exact ⟨a, b, alternatives_of_local_transitive d b a hs hU₀ hlocal⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
