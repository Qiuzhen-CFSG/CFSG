module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootActionModel

/-!
# Semilinear coordinates on the original triality arms root

A torus-preserving parabolic automorphism carries the marked arms reflection
into its torus coset. Its proved additive action on the positive cubic root
therefore determines an additive action on the negative root. The faithful
rank-one SL₂ map and its braid and diagonal relations force a single cubic
field automorphism, with reciprocal scalars on the two signs.

For an involutive local automorphism the coefficient squares to one and the
root scalar has norm one. The companion source module uses the original
right quotient to prove that an involution outside S has nontrivial coefficient.
No automorphism of the full triality carrier is assumed or constructed here.
Identifying the central root coefficient and the action on the whole positive
subgroup remains necessary for the existing fixed-point bound.

Source: Aschbacher--Smith F.4.29 and F.4.37--38, printed pp.289,293--294
(`refs/quasithin.pdf`); Steinberg Theorem 30(2),(4) and Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`, pp.162--164 and 197--198.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.ElementaryCentralKernel
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityLocalParameters

/-- The literal signed simple root, included in its own parabolic. -/
@[expose] def rootInParabolic (P : Parameters) (hp : P.prime=2)
    (s : Bool) (i : Node) (r : RootField P i) : parabolic P i :=
  ⟨rootElement P hp s i r, by
    cases s
    · exact negative_mem_parabolic P hp i r
    · exact borel_le_parabolic P i (unipotent_le_borel P (positive_mem_unipotent P hp i r))⟩

private def rankOneLocal (P : Parameters) (hp : P.prime=2) (i : Node) :
    SL(2, RootField P i) →* parabolic P i :=
  (rankOne P hp i).codRestrict _ (by
    intro g
    apply sl2_root_induction (fun g => rankOne P hp i g ∈ parabolic P i) ?_ ?_ ?_ g
    · intro r
      change rankOne P hp i (signed true r) ∈ _
      rw [rankOne_signed]
      exact (rootInParabolic P hp true i r).property
    · intro r
      change rankOne P hp i (signed false r) ∈ _
      rw [rankOne_signed]
      exact (rootInParabolic P hp false i r).property
    · intro x y hx hy
      rw [map_mul]
      exact (parabolic P i).mul_mem hx hy)

private theorem rankOneLocal_signed (P : Parameters) (hp : P.prime=2)
    (s : Bool) (i : Node) (r : RootField P i) :
    rankOneLocal P hp i (signed s r)=rootInParabolic P hp s i r :=
  Subtype.ext (rankOne_signed P hp s i r)

private theorem negative_action_of_positive (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (i : Node) (b : MulAut (parabolic (binaryParameters n hn) i))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) i)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) i))
    (u : RootField (binaryParameters n hn) i ≃+ RootField (binaryParameters n hn) i)
    (hu : ∀ r, b (rootInParabolic (binaryParameters n hn) rfl true i r)=
      rootInParabolic (binaryParameters n hn) rfl true i (u r)) :
    ∃ v : RootField (binaryParameters n hn) i ≃+ RootField (binaryParameters n hn) i,
      ∀ r, b (rootInParabolic (binaryParameters n hn) rfl false i r)=
        rootInParabolic (binaryParameters n hn) rfl false i (v r) := by
  let P := binaryParameters n hn
  let w : parabolic P i := ⟨simpleRepresentative P rfl i,simpleRepresentative_mem_parabolic P rfl i⟩
  obtain ⟨d,hd⟩ := TrialityWeylAction.parabolic_aut_weyl n hn hn2 i b hD
  obtain ⟨a,ha⟩ := (TorusCoordinates.torusMulEquiv P rfl).surjective d
  let c := (nodeCharacter P a i).val⁻¹
  have hc : c≠0 := inv_ne_zero (nodeCharacter P a i).ne_zero
  let v : RootField P i ≃+ RootField P i :=
    { toEquiv := u.toEquiv.trans (Equiv.mulLeft₀ c hc)
      map_add' := fun r s => by change c*u (r+s)=c*u r+c*u s; rw [map_add,mul_add] }
  refine ⟨v,?_⟩
  intro r
  have hw : w⁻¹=w := by
    apply Subtype.ext
    exact inv_eq_of_mul_eq_one_right (by
      rw [←pow_two]
      exact simpleRepresentative_sq P rfl i)
  have he (r) : w*rootInParabolic P rfl true i r*w⁻¹=rootInParabolic P rfl false i r := by
    rw [hw]
    exact Subtype.ext (simpleRepresentative_positive P rfl i r)
  rw [←he r,map_mul,map_mul,map_inv,hu]
  apply Subtype.ext
  change (b w).val*rootElement P rfl true i (u r)*(b w).val⁻¹=_
  rw [hd]
  calc
    _ = d.val*(simpleRepresentative P rfl i*rootElement P rfl true i (u r)*
        (simpleRepresentative P rfl i)⁻¹)*d.val⁻¹ := by dsimp only [P]; group
    _ = d.val*rootElement P rfl false i (u r)*d.val⁻¹ := by
      rw [show (simpleRepresentative P rfl i)⁻¹=simpleRepresentative P rfl i from congrArg Subtype.val hw,
        simpleRepresentative_positive P rfl i (u r)]
    _ = rootElement P rfl false i (v r) := by
      rw [←congrArg Subtype.val ha,torus_root_conjugate P rfl a false i (u r)]
      rfl

/-- The two signed cubic roots have reciprocal scalars and the same field map. -/
theorem arms_signed_field_action (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .arms))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms)) :
    ∃ (c : (ExtensionField (binaryParameters n hn))ˣ)
      (σ : ExtensionField (binaryParameters n hn) ≃+* ExtensionField (binaryParameters n hn)),
      ∀ s r, b (rootInParabolic (binaryParameters n hn) rfl s .arms r)=
        rootInParabolic (binaryParameters n hn) rfl s .arms (signedScalar s c.val * σ r) := by
  let P := binaryParameters n hn
  obtain ⟨u,hu⟩ := TrialityRootAction.arms_root_action n hn hn2 b hD hU
  have hu' (r) : b (rootInParabolic P rfl true .arms r)=rootInParabolic P rfl true .arms (u r) :=
    Subtype.ext (hu r)
  obtain ⟨v,hv⟩ := negative_action_of_positive n hn hn2 .arms b hD u hu'
  have hp (r) : b (rankOneLocal P rfl .arms (upper r))=rankOneLocal P rfl .arms (upper (u r)) := by
    change b (rankOneLocal P rfl .arms (signed true r))=rankOneLocal P rfl .arms (signed true (u r))
    rw [rankOneLocal_signed P rfl true .arms r,rankOneLocal_signed P rfl true .arms (u r)]
    exact hu' r
  have hn' (r) : b (rankOneLocal P rfl .arms (lower r))=rankOneLocal P rfl .arms (lower (v r)) := by
    change b (rankOneLocal P rfl .arms (signed false r))=rankOneLocal P rfl .arms (signed false (v r))
    rw [rankOneLocal_signed P rfl false .arms r,rankOneLocal_signed P rfl false .arms (v r)]
    exact hv r
  obtain ⟨c,σ,hp',hn'⟩ := exists_rankOne_field (rankOneLocal P rfl .arms)
    (fun _ _ h => rankOne_injective P rfl .arms (congrArg Subtype.val h)) b u v hp hn'
  refine ⟨c,σ,?_⟩
  intro s r
  cases s
  · simpa only [signedScalar,Bool.false_eq_true,if_false,hn' r] using hv r
  · simpa only [signedScalar,if_true,hp' r] using hu' r

/-- Involutivity forces the cubic coefficient to square to one and the scalar
to have norm one for that coefficient. -/
theorem arms_involution_field_action (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .arms))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (hb : Function.Involutive b) :
    ∃ (c : (ExtensionField (binaryParameters n hn))ˣ)
      (σ : ExtensionField (binaryParameters n hn) ≃+* ExtensionField (binaryParameters n hn)),
      σ^2=1 ∧ c.val*σ c.val=1 ∧
      ∀ s r, b (rootInParabolic (binaryParameters n hn) rfl s .arms r)=
        rootInParabolic (binaryParameters n hn) rfl s .arms (signedScalar s c.val * σ r) := by
  let P := binaryParameters n hn
  obtain ⟨c,σ,ha⟩ := arms_signed_field_action n hn hn2 b hD hU
  have hu (r) : b (rootInParabolic P rfl true .arms r)=
      rootInParabolic P rfl true .arms (c.val*σ r) := ha true r
  have hpair (r) : c.val*σ (c.val*σ r)=r := by
    have he : rootInParabolic P rfl true .arms (c.val*σ (c.val*σ r))=
        rootInParabolic P rfl true .arms r := by rw [←hu,←hu,hb]
    exact rootElement_injective P rfl true .arms (congrArg Subtype.val he)
  have hc : c.val*σ c.val=1 := by simpa only [map_one,mul_one] using hpair 1
  have hs : σ^2=1 := by
    ext r
    change σ (σ r)=r
    simpa only [map_mul,←mul_assoc,hc,one_mul] using hpair r
  exact ⟨c,σ,hs,hc,ha⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityLocalParameters
