module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.OrthogonalA5
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.CommutingFactors
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSevenSource
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSixTensorSource

/-!
# Rank exclusions for the three imprimitive binary eight-spaces

For the S₇ case, the actual A₇ four-space and its odd conjugate give rank four
on involutions. The source adapter also works directly on any invariant
four-dimensional summand P in V = P ⊕ xP, constructing the swap coordinates
and deriving equal blocks from commutativity in X.

For the A₆ × C₃ extension, inner involutions have their natural A₆ rank doubled
on the tensor product. An outer involution inverts the fixed-point-free cubic
factor and therefore moves half the space. The source adapter identifies only
the product restriction; it does not assume an outer action or a rank bound.

For the A₅ product, the orthogonal four-space is the five-point even-weight
core. Commutation with the swapping involution forces the two block actions
of an element of X to agree. The generation statement
`X = <x> (X ∩ (A5 × A5))` supplies the two-coset form. The final source adapter
constructs the second summand coordinates from x. Its commutator-space version
derives the second-factor fixation from the disjointness of [V,L] and [V,Lˣ],
so it prescribes only the actual orthogonal action of the first factor. The restriction to X is essential: an involution in only one
factor of the unrestricted product has rank two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(8),(10),(12), printed p.364/PDF p.375, and the proof of 6.2.19,
printed p.691/PDF p.708. The exports use actual representations and group or
module identifications, rather than group-family labels.
-/

@[expose] public section

namespace Representation.RankTwo.Imprimitive
open OrthogonalA5

/-- Operators of the natural imprimitive action of A5 wr C2. -/
def wreathOperator (p q : Alternating) (s : Bool) :
    Module.End (ZMod 2) (Space × Space) :=
  if s then swap (LinearEquiv.refl (ZMod 2) Space) *
    (representation p).prodMap (representation q)
  else (representation p).prodMap (representation q)

lemma finrank_wreathOperator (p q : Alternating) (s : Bool)
    (h2 : wreathOperator p q s * wreathOperator p q s = 1)
    (hc : Commute (wreathOperator p q s) (swap (LinearEquiv.refl (ZMod 2) Space))) :
    Module.finrank (ZMod 2) (LinearMap.range (wreathOperator p q s - 1)) = 0 ∨
    Module.finrank (ZMod 2) (LinearMap.range (wreathOperator p q s - 1)) = 4 := by
  cases s with
  | false => exact OrthogonalA5.finrank_commuting_block p (representation q) hc h2
  | true =>
    right
    rw [finrank_of_exchanges (wreathOperator p q true) (representation p) (representation q)
      (fun v w => rfl) h2, finrank_space]

lemma wreathOperator_not_rankTwo (p q : Alternating) (s : Bool)
    (h2 : wreathOperator p q s * wreathOperator p q s = 1)
    (hc : Commute (wreathOperator p q s) (swap (LinearEquiv.refl (ZMod 2) Space))) :
    Module.finrank (ZMod 2) (LinearMap.range (wreathOperator p q s - 1)) ≠ 2 := by
  rcases finrank_wreathOperator p q s h2 hc with h | h <;> omega

/-- The X restriction is essential: its commutativity forces the block actions
onto the diagonal. The normal form is the source X = <x>(X ∩ (A5 × A5)). -/
lemma orthogonalA5_X_not_rankTwo {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H (Space × Space))
    (i : (Alternating × Alternating) →* H) (X : Subgroup H) (x : H)
    (hx : x ∈ X)
    (hxact : ρ x = swap (LinearEquiv.refl (ZMod 2) Space))
    (hiact : ∀ p q, ρ (i (p,q)) = (representation p).prodMap (representation q))
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hnormal : ∀ g ∈ X, ∃ p q, g = i (p,q) ∨ g = x * i (p,q))
    (g : H) (hg : g ∈ X) : Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  have h2 : ρ g * ρ g = 1 := by rw [← map_mul, hX2 g hg, map_one]
  have hc : Commute (ρ g) (swap (LinearEquiv.refl (ZMod 2) Space)) := by
    rw [← hxact]
    exact (hXcomm g hg x hx).map ρ
  obtain ⟨p,q,he | he⟩ := hnormal g hg
  · have hact : ρ g = wreathOperator p q false := by rw [he, hiact]; rfl
    rw [hact] at h2 hc
    have hn : Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) ≠ 2 := by
      rw [hact]
      exact wreathOperator_not_rankTwo p q false h2 hc
    exact hn
  · have hact : ρ g = wreathOperator p q true := by rw [he, map_mul, hxact, hiact]; rfl
    rw [hact] at h2 hc
    have hn : Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) ≠ 2 := by
      rw [hact]
      exact wreathOperator_not_rankTwo p q true h2 hc
    exact hn
/-- Elementary abelian generation by an involution and a subgroup gives two cosets. -/
lemma two_coset_normal_form {H : Type*} [Group H]
    (X A : Subgroup H) (x : H) (hx : x ∈ X) (hA : A ≤ X)
    (h2 : ∀ g ∈ X, g * g = 1)
    (hc : ∀ g ∈ X, Commute g x)
    (hgen : X = Subgroup.zpowers x ⊔ A) (g : H) (hg : g ∈ X) :
    ∃ a ∈ A, g = a ∨ g = x * a := by
  have hcl : Subgroup.closure (insert x (A : Set H)) = X := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.closure_eq,
      ← Subgroup.zpowers_eq_closure]
    exact hgen.symm
  have hgcl : g ∈ Subgroup.closure (insert x (A : Set H)) := by rwa [hcl]
  refine Subgroup.closure_induction (p := fun g _ => ∃ a ∈ A, g = a ∨ g = x * a)
    ?_ ?_ ?_ ?_ hgcl
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · subst a
      exact ⟨1, A.one_mem, Or.inr (mul_one x).symm⟩
    · exact ⟨a, ha, Or.inl rfl⟩
  · exact ⟨1, A.one_mem, Or.inl rfl⟩
  · intro u v _ _ hu hv
    obtain ⟨a, ha, hua⟩ := hu
    obtain ⟨b, hb, hvb⟩ := hv
    rcases hua with hua | hua <;> rcases hvb with hvb | hvb <;> rw [hua, hvb]
    · exact ⟨a * b, A.mul_mem ha hb, Or.inl rfl⟩
    · refine ⟨a * b, A.mul_mem ha hb, Or.inr ?_⟩
      rw [← mul_assoc, (hc a (hA ha)).eq, mul_assoc]
    · exact ⟨a * b, A.mul_mem ha hb, Or.inr (mul_assoc x a b)⟩
    · refine ⟨a * b, A.mul_mem ha hb, Or.inl ?_⟩
      calc
        (x * a) * (x * b) = (x * (a * x)) * b := by simp only [mul_assoc]
        _ = (x * (x * a)) * b := by rw [(hc a (hA ha)).eq]
        _ = a * b := by rw [← mul_assoc x x a, h2 x hx, one_mul]
  · intro a ha ih
    have haX : a ∈ X := by rwa [hcl] at ha
    rw [inv_eq_of_mul_eq_one_left (h2 a haX)]
    exact ih

/-- Case-(12) calculation from the source generation statement, with the
actual A5 product action. The normal form is derived, not assumed. -/
lemma orthogonalA5_generated_X_not_rankTwo {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H (Space × Space))
    (i : (Alternating × Alternating) →* H) (X : Subgroup H) (x : H)
    (hx : x ∈ X)
    (hxact : ρ x = swap (LinearEquiv.refl (ZMod 2) Space))
    (hiact : ∀ p q, ρ (i (p,q)) = (representation p).prodMap (representation q))
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hgen : X = Subgroup.zpowers x ⊔ (X ⊓ i.range))
    (g : H) (hg : g ∈ X) : Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  apply orthogonalA5_X_not_rankTwo ρ i X x hx hxact hiact hX2 hXcomm ?_ g hg
  intro a ha
  obtain ⟨b, hb, hab⟩ := two_coset_normal_form X (X ⊓ i.range) x hx inf_le_left
    hX2 (fun g hg => hXcomm g hg x hx) hgen a ha
  obtain ⟨⟨p,q⟩, rfl⟩ := hb.2
  exact ⟨p,q,hab⟩

/-- Case (12) in source submodule coordinates. The complement is the image of
P under x. Only the first product action is prescribed; X commutativity forces
the second action for elements in X onto the diagonal. -/
theorem orthogonalA5_source_X_not_rankTwo
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (Alternating × Alternating) →* H)
    (P : Submodule (ZMod 2) V) (eP : P ≃ₗ[ZMod 2] Space)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hsplit : IsCompl P (P.map (ρ x)))
    (hfirst : ∀ p q (v : Space),
      ρ (i (p,q)) (eP.symm v : P) = (eP.symm (representation p v) : P))
    (hgen : X = Subgroup.zpowers x ⊔ (X ⊓ i.range))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  have hx2 : ρ x * ρ x = 1 := by rw [← map_mul, hX2 x hx, map_one]
  let f : (Space × Space) ≃ₗ[ZMod 2] V :=
    (eP.symm.prodCongr eP.symm).trans (swappedCoordinates (ρ x) hx2 P hsplit)
  have hswap (v w : Space) : ρ x (f (v,w)) = f (w,v) :=
    swappedCoordinates_swap (ρ x) hx2 P hsplit (eP.symm v) (eP.symm w)
  have hinner (p q : Alternating) (hb : i (p,q) ∈ X) (v w : Space) :
      ρ (i (p,q)) (f (v,w)) = f (representation p v, representation p w) := by
    change ρ (i (p,q)) ((eP.symm v : P) + ρ x (eP.symm w : P)) =
      (eP.symm (representation p v) : P) + ρ x (eP.symm (representation p w) : P)
    have hc (z : V) : ρ (i (p,q)) (ρ x z) = ρ x (ρ (i (p,q)) z) :=
      LinearMap.congr_fun ((hXcomm _ hb x hx).map ρ).eq z
    rw [map_add, hc, hfirst, hfirst]
  obtain ⟨b, hb, hgb⟩ := two_coset_normal_form X (X ⊓ i.range) x hx inf_le_left
    hX2 (fun g hg => hXcomm g hg x hx) hgen g hg
  obtain ⟨⟨p,q⟩, rfl⟩ := hb.2
  rcases hgb with rfl | rfl
  · let a := (representation p).prodMap (representation p)
    have ha2 : a * a = 1 := by
      apply LinearMap.ext
      intro z
      apply f.injective
      have h2 : ρ (i (p,q)) * ρ (i (p,q)) = 1 := by
        rw [← map_mul, hX2 _ hb.1, map_one]
      have he : ρ (i (p,q)) (ρ (i (p,q)) (f z)) = f z := LinearMap.congr_fun h2 (f z)
      rw [hinner p q hb.1 z.1 z.2, hinner p q hb.1] at he
      exact he
    have hc : Commute a (swap (LinearEquiv.refl (ZMod 2) Space)) := by
      apply LinearMap.ext
      rintro ⟨v,w⟩
      rfl
    have hr := (displacementRangeEquiv f a (ρ (i (p,q)))
      (fun z => hinner p q hb.1 z.1 z.2)).finrank_eq
    exact fun htwo => wreathOperator_not_rankTwo p p false ha2 hc (hr.trans htwo)
  · have hact (v w : Space) :
        ρ (x * i (p,q)) (f (v,w)) = f (representation p w, representation p v) := by
      rw [map_mul, Module.End.mul_apply, hinner p q hb.1, hswap]
    have hr := finrank_of_exchanging_coordinates f (ρ (x * i (p,q)))
      (representation p) (representation p) hact (by rw [← map_mul, hX2 _ hg, map_one])
    rw [finrank_space] at hr
    exact fun htwo => (by decide : (4 : ℕ) ≠ 2) (hr.symm.trans htwo)

open BinaryOffender

open OrthogonalA5 in
/-- The literal case-(12) decomposition by [V,L] and [V,Lˣ] discharges the
second-factor action and exchanged-coordinate premises of the rank adapter. -/
theorem orthogonalA5_commutator_X_not_rankTwo
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (Alternating × Alternating) →* H)
    (eP : (subspaceCommutator ρ ⊤
      (i.comp (MonoidHom.inl Alternating Alternating)).range) ≃ₗ[ZMod 2] Space)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hconj : ∀ p : Alternating, x * i (p,1) * x⁻¹ = i (1,p))
    (hsplit : IsCompl
      (subspaceCommutator ρ ⊤ (i.comp (MonoidHom.inl Alternating Alternating)).range)
      (subspaceCommutator ρ ⊤ (i.comp (MonoidHom.inr Alternating Alternating)).range))
    (hfirst : ∀ p (v : Space),
      ρ (i (p,1)) (eP.symm v : V) = (eP.symm (representation p v) : V))
    (hgen : X = Subgroup.zpowers x ⊔ (X ⊓ i.range))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  apply orthogonalA5_source_X_not_rankTwo ρ i _ eP X x hx hX2 hXcomm ?_ ?_ hgen g hg
  · rwa [map_commutator_of_swaps_factors ρ i x (hX2 x hx) hconj]
  · intro p q v
    have hfix : ρ (i (1,q)) (eP.symm v : V) = (eP.symm v : V) := by
      apply fixes_commutator_of_disjoint ρ _ _ ?_ hsplit.disjoint
        (i (1,q)) ⟨q,rfl⟩ (eP.symm v) (eP.symm v).property
      rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
      exact (show Commute (a,1) (1,b) from by simp [Commute, SemiconjBy]).map i
    have he : i (p,q) = i (p,1) * i (1,q) := by rw [← map_mul]; simp
    rw [he, map_mul, Module.End.mul_apply, hfix, hfirst]

end Representation.RankTwo.Imprimitive
