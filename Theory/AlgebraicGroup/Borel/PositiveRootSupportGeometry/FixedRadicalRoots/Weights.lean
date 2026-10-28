module

public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.Tori.Character.ConnectedKernel
public import Theory.AlgebraicGroup.Bor1.GeometricCertificates
public import Theory.AlgebraicGroup.Unipotent.Radical

/-!
Character-kernel containments for the actual realized root subgroups.

The integral self-coroot pairing is two, so a realized root character is
nontrivial in every characteristic. Its connected kernel is therefore a
codimension-one subtorus. The raw inverse-conjugation weight equation shows
that this kernel centralizes the root subgroup. If the root subgroup lies
in a Borel, it lies in the Borel radical and hence in the corresponding
fixed radical. These are containments, without an assertion of uniqueness.

Sources: Borel, *Linear Algebraic Groups*, IV, 13.18(4); GLS3,
Definitions 1.9.1--1.9.3 and Remarks 1.9.6. Integral character evaluation
is retained, with no differentiation or separability assumption.
-/

universe u
namespace Theory.AlgebraicGroup.BorelFixedRadicalRoots
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- Integral self-coroot evaluation excludes the trivial character, also in
characteristic two. -/
public theorem realized_rootWeight_ne_one {D : RootGroupData G T}
    (hD : D.IsRealization) (a : D.Root) : D.rootWeight a ≠ 1 := by
  intro h
  have hp := hD.weightPairing_rootWeight a a
  rw [h, hD.weightPairing_one] at hp
  have haa := hD.2.2.2.2.2.2.1 a
  omega

omit [IsAlgClosed k] in
private theorem parameter_surjective {X : ClosedSubgroup G}
    (p : OneParameterParametrization X.carrierVariety) :
    Function.Surjective p.value := by
  intro x
  refine ⟨Multiplicative.toAdd (additiveGroupPointEquiv k (p.inv.onPoints x)), ?_⟩
  change p.hom.onPoints _ = x
  have heq : kPlusPoint (Multiplicative.toAdd
      (additiveGroupPointEquiv k (p.inv.onPoints x))) = p.inv.onPoints x := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  rw [heq, p.inv_hom_id]

omit [IsAlgClosed k] in
/-- A root subgroup is centralized by any subgroup on which its full
algebraic character is trivial. -/
public theorem root_le_centralizer_of_weight_trivial {X Q : ClosedSubgroup G}
    (hX : IsTorusRootSubgroup T X) {chi : TorusWeight T}
    (hchi : RootWeightEquation T X chi) (hQT : Q ≤ T)
    (htriv : ∀ t : Variety.Point T.carrierVariety,
      T.includePoint t ∈ Q → chi.pointCharacter t = 1) : X ≤ Q.centralizer := by
  let p : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
  intro x hx
  obtain ⟨a, ha⟩ := parameter_surjective p (X.pointEquiv.symm ⟨x, hx⟩)
  have hxa : X.includePoint (p.value a) = x := by rw [ha]; rfl
  change x ∈ Subgroup.centralizer (Q.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  let t := T.pointEquiv.symm ⟨q, hQT hq⟩
  have ht : T.includePoint t = q := rfl
  have heq := hchi p a t
  rw [htriv t (by rwa [ht]), one_mul, hxa, ht] at heq
  calc
    q * x = q * (q⁻¹ * x * q) := congrArg (q * ·) heq.symm
    _ = x * q := by group

/-- Every root subgroup lies in the centralizer of its character kernel
identity component, mapped through the actual torus inclusion. -/
public theorem root_le_connectedKernel_centralizer {X : ClosedSubgroup G}
    (hT : IsSubtorus T) (hX : IsTorusRootSubgroup T X)
    {chi : TorusWeight T} (hchi : RootWeightEquation T X chi) (hne : chi ≠ 1) :
    X ≤ (chi.ambientConnectedKernel T).centralizer := by
  have hK := chi.connectedKernel_codimension_one T hT hne
  apply root_le_centralizer_of_weight_trivial hX hchi hK.ambientConnectedKernel_le
  intro t ht
  obtain ⟨s, hs, hst⟩ := (hK.mem_ambientConnectedKernel_iff _).mp ht
  have hst' : s = t := T.inclusion_injective hst
  subst s
  have hker := chi.kernelClosedSubgroup.identityComponentAmbient_le hs
  have heq : chi.onPoints t = 1 := hker
  change (dPointEquiv 1 (chi.onPoints t) 0 : k) = 1
  rw [heq, dPointEquiv_one]
  rfl

/-- The chosen realized root subgroup lies in the corresponding connected
character-kernel centralizer. -/
public theorem realized_root_le_connectedKernel_centralizer {D : RootGroupData G T}
    (hT : IsSubtorus T) (hD : D.IsRealization) (a : D.Root) :
    D.rootSubgroup a ≤ ((D.rootWeight a).ambientConnectedKernel T).centralizer :=
  root_le_connectedKernel_centralizer hT (hD.2.2.1 a).1 (hD.2.2.1 a).2
    (realized_rootWeight_ne_one hD a)


/-- A realized root contained in a Borel lies in its radical fixed by the
connected character kernel. This is the concrete Borel-radical application. -/
public theorem realized_root_le_fixed_radical_of_le_borel {D : RootGroupData G T}
    (hD : D.IsRealization) (hT : IsSubtorus T) {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (a : D.Root) (ha : D.rootSubgroup a ≤ B) :
    D.rootSubgroup a ≤ U.pointwiseCentralizer ((D.rootWeight a).ambientConnectedKernel T) := by
  have hroot := (hD.2.2.1 a).1
  have hRU := hU.contains_unipotent_closedSubgroup hB.connected hB.solvable ha
    hroot.2.isUnipotentAlgebraicGroup
  have hRC := realized_root_le_connectedKernel_centralizer hT hD a
  exact fun _ hx => ⟨hRU hx, hRC hx⟩

end Theory.AlgebraicGroup.BorelFixedRadicalRoots
