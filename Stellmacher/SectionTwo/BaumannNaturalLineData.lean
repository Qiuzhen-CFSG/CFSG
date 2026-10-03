module
public import Stellmacher.SectionOne.OneSevenCoordinateActionLines

/-!
# Native commutator lines of the Baumann factor family

Let V ≤ B in a finite group H, with an action of a finite group X on V.
Suppose f : B → X has kernel V inside B and image T ∩ E, where T is a
Sylow two-subgroup and E is a normal internal product of one-seven factors.
The given action of f(b) on V must agree with conjugation by b in H.
Assume this action is faithful and distinct factor supports are disjoint.

The preimages of the factor Sylow lines give subgroups Ti ≤ B such that
B = V ∨ ⋁ Ti. For the original factor supports Vi, viewed inside H, the
intrinsic action-line theorem transports to [V,Ti] = [Vi,B] and |[Vi,B]|=2.
The kernel/image correspondence proves generation, including the empty
family case. A direct generator calculation transports action commutators
through f using its supplied conjugation formula; injectivity of V's
subtype map preserves the line cardinalities.

No replacement action or factor family is constructed. The conclusion is
the native input to the automorphism permutation of commutator lines in
Stellmacher (4.6), journal p.26, from the factors in (2.2), p.20.
Source: refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionTwo
universe u

private theorem native_action_commutator_map
    {H X : Type u} [Group H] [Group X] (B V : Subgroup H)
    [MulDistribMulAction X V] (f : B →* X)
    (hact : ∀ b : B, ∀ v : V, ((f b • v : V) : H) = b * (v : H) * (b : H)⁻¹)
    (A : Subgroup B) (W : Subgroup V) :
    (commutatorSubgroup (A.map f) V W).map V.subtype =
      ⁅W.map V.subtype, A.map B.subtype⁆ := by
  rw [commutatorSubgroup, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨a, w, hw, rfl⟩, rfl⟩
    obtain ⟨a₀, ha₀, heq⟩ := a.property
    refine ⟨(w : H)⁻¹,
      Subgroup.mem_map_of_mem V.subtype (W.inv_mem hw),
      (a₀ : H), Subgroup.mem_map_of_mem B.subtype ha₀, ?_⟩
    rw [commutatorElement_def]
    change (w : H)⁻¹ * (a₀ : H) * (w : H)⁻¹⁻¹ * (a₀ : H)⁻¹ =
      ((w⁻¹ * (a.val • w) : V) : H)
    rw [← heq]
    change (w : H)⁻¹ * (a₀ : H) * (w : H)⁻¹⁻¹ * (a₀ : H)⁻¹ =
      (w : H)⁻¹ * ((f a₀ • w : V) : H)
    rw [hact]
    group
  · rintro ⟨_, ⟨w₀, hw₀, rfl⟩, _, ⟨a₀, ha₀, rfl⟩, rfl⟩
    let abar : A.map f := ⟨f a₀, Subgroup.mem_map_of_mem f ha₀⟩
    refine ⟨(w₀⁻¹)⁻¹ * (abar • w₀⁻¹),
      ⟨abar, w₀⁻¹, W.inv_mem hw₀, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    change (w₀ : H)⁻¹⁻¹ * ((f a₀ • w₀⁻¹ : V) : H) =
      (w₀ : H) * (a₀ : H) * (w₀ : H)⁻¹ * (a₀ : H)⁻¹
    rw [hact]
    change (w₀ : H)⁻¹⁻¹ * ((a₀ : H) * (w₀ : H)⁻¹ * (a₀ : H)⁻¹) = _
    group

private theorem preimage_coordinates_generate
    {H X : Type u} [Group H] [Group X] (B V : Subgroup H)
    (hVB : V ≤ B) (f : B →* X) (hker : f.ker = V.subgroupOf B)
    {n : ℕ} (Q : Fin n → Subgroup X) (hQ : f.range = ⨆ i, Q i) :
    B = V ⊔ ⨆ i, (Q i |>.comap f).map B.subtype := by
  let U := V.subgroupOf B ⊔ ⨆ i, (Q i).comap f
  have hQi (i : Fin n) : Q i ≤ f.range := by
    rw [hQ]
    exact le_iSup Q i
  have hUmap : U.map f = f.range := by
    have hk : f.ker.map f = ⊥ := Subgroup.map_ker_self f
    dsimp only [U]
    rw [Subgroup.map_sup, Subgroup.map_iSup, ← hker]
    simp only [hk, bot_sup_eq, Subgroup.map_comap_eq_self (hQi _), ← hQ]
  have hUtop : U = ⊤ := by
    apply Subgroup.map_injective_of_ker_le f (hker ▸ le_sup_left) le_top
    simpa only [← MonoidHom.range_eq_map] using hUmap
  have hm := congrArg (fun A : Subgroup B => A.map B.subtype) hUtop
  dsimp only [U] at hm
  rw [Subgroup.map_sup, Subgroup.map_iSup,
    Subgroup.map_subgroupOf_eq_of_le hVB, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hm
  exact hm.symm

public theorem baumann_natural_line_data
    {H X : Type u} [Group H] [Finite H] [Group X] [Finite X]
    (B V : Subgroup H) [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (hVB : V ≤ B) (f : B →* X) (hker : f.ker = V.subgroupOf B)
    (T : Sylow 2 X) (E : Subgroup X) (hEnormal : E.Normal)
    (hrange : f.range = (T : Subgroup X) ⊓ E)
    (hact : ∀ b : B, ∀ v : V, ((f b • v : V) : H) = b * (v : H) * (b : H)⁻¹)
    {n : ℕ} (D : Fin n → Subgroup X)
    (hprod : IsInternalDirectProductFamily E D)
    (hD : ∀ i, SectionOne.IsOneSevenFactor (V := V) (D i))
    (hfaith : fixingSubgroup X (Set.univ : Set V) = ⊥)
    (hdisj : Pairwise fun i j =>
      Disjoint (commutatorAction (D i) V) (commutatorAction (D j) V)) :
    ∃ Ti : Fin n → Subgroup H,
      (∀ i, Ti i ≤ B) ∧ B = V ⊔ ⨆ i, Ti i ∧
      ∀ i, ⁅V, Ti i⁆ = ⁅(commutatorAction (D i) V).map V.subtype, B⁆ ∧
        Nat.card (⁅(commutatorAction (D i) V).map V.subtype, B⁆ : Subgroup H) = 2 := by
  have hlines := SectionOne.oneSevenFactor_sylow_coordinate_action_lines
    hfaith T E hEnormal D hprod hD hdisj
  let Q (i : Fin n) := (T : Subgroup X) ⊓ D i
  let Ti (i : Fin n) := ((Q i).comap f).map B.subtype
  have hcoord := SectionOne.sl2_family_sylow_coordinates T E hEnormal D (hprod) (fun i => (hD i).1)
  have hQi (i : Fin n) : Q i ≤ f.range := by
    rw [hrange]
    exact le_inf inf_le_left (inf_le_right.trans (by rw [hprod.1]; exact le_iSup D i))
  refine ⟨Ti, fun i => Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact preimage_coordinates_generate B V hVB f hker Q (hrange.trans hcoord.1)
  · intro i
    have hsmall : (commutatorAction (Q i) V).map V.subtype = ⁅V, Ti i⁆ := by
      have hm := native_action_commutator_map B V f hact ((Q i).comap f) ⊤
      rw [Subgroup.map_comap_eq_self (hQi i), ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at hm
      exact hm
    have hbig : (commutatorSubgroup (↥((T : Subgroup X) ⊓ E)) V
        (commutatorAction (D i) V)).map V.subtype =
        ⁅(commutatorAction (D i) V).map V.subtype, B⁆ := by
      have hm := native_action_commutator_map B V f hact ⊤ (commutatorAction (D i) V)
      rw [← MonoidHom.range_eq_map, hrange, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at hm
      exact hm
    have heq := congrArg (fun W : Subgroup V => W.map V.subtype) (hlines i).1
    change _ = (commutatorAction (Q i) V).map V.subtype at heq
    rw [hbig, hsmall] at heq
    refine ⟨heq.symm, ?_⟩
    rw [heq, ← hsmall, Subgroup.card_map_of_injective V.subtype_injective]
    exact (hlines i).2

end Stellmacher.SectionTwo

