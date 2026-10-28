module

public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.PointOrbit
public import Theory.GroupAction.CosetTransport
public import Theory.SpecificGroups.FifteenPointSubgroups.Orders
public import Theory.SpecificGroups.FifteenPointSubgroups.Actions

/-!
# Left-coset transport and the fifteen-point stabilizer actions

The literal vector stabilizer gives an equivariant equivalence between its
left cosets and the original representation orbit. The source hypotheses
already imply that this orbit has fifteen points. Two-transitivity transports
without faithfulness, spanning, irreducibility or a parabolic assumption.

The concrete PSL₄(2) endpoint-parabolic and A₇ subgroup actions discharge
both model branches. `pairTransitiveOrbit_of_models` gives the original
representation orbit's two-transitivity and size, and
`fifteenPointStabilizerInput` proves the full action input for B.4.12(2).
The conditional assembly APIs are retained for independent reuse.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.4.12(2), printed p.97 of `refs/quasithin.pdf`.
-/

public section
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.SmallRecognition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

@[instance_reducible] private def representationAction (ρ : Representation (ZMod 2) G V) : MulAction G V where
  smul g v := ρ g v
  one_smul v := by change ρ 1 v = v; simp
  mul_smul g h v := by change ρ (g*h) v = ρ g (ρ h v); simp only [map_mul, Module.End.mul_apply]

noncomputable def vectorCosetEquiv (ρ : Representation (ZMod 2) G V) (v : V) :
    G ⧸ vectorStabilizer ρ v ≃ Set.range (fun g => ρ g v) := by
  letI := representationAction ρ
  exact (MulAction.orbitEquivQuotientStabilizer G v).symm

theorem vectorCosetEquiv_mk (ρ : Representation (ZMod 2) G V) (v : V) (g : G) :
    (vectorCosetEquiv ρ v (QuotientGroup.mk g) : V) = ρ g v := by
  let := representationAction ρ
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply G v g

theorem vectorCosetEquiv_smul (ρ : Representation (ZMod 2) G V) (v : V)
    (g : G) (q : G ⧸ vectorStabilizer ρ v) :
    (vectorCosetEquiv ρ v (g • q) : V) = ρ g (vectorCosetEquiv ρ v q) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change (vectorCosetEquiv ρ v (QuotientGroup.mk (g*a)) : V) = _
    simp only [vectorCosetEquiv_mk, map_mul, Module.End.mul_apply]

theorem vector_orbit_card_eq_index (ρ : Representation (ZMod 2) G V) (v : V) :
    Nat.card (Set.range fun g => ρ g v) = (vectorStabilizer ρ v).index :=
  Nat.card_congr (vectorCosetEquiv ρ v).symm

theorem pairTransitiveOrbit_of_cosets (ρ : Representation (ZMod 2) G V) (v : V)
    (ht : MulAction.IsMultiplyPretransitive G (G ⧸ vectorStabilizer ρ v) 2) :
    Representation.PairTransitiveOrbit ρ v := by
  intro a ha b hb hab c hc d hd hcd
  let f := vectorCosetEquiv ρ v
  have hab' : f.symm ⟨a, ha⟩ ≠ f.symm ⟨b, hb⟩ := by
    intro h
    exact hab (congrArg Subtype.val (f.symm.injective h))
  have hcd' : f.symm ⟨c, hc⟩ ≠ f.symm ⟨d, hd⟩ := by
    intro h
    exact hcd (congrArg Subtype.val (f.symm.injective h))
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp ht hab' hcd'
  refine ⟨g, ?_, ?_⟩
  · have hh := congrArg (fun q => (f q : V)) hga
    simpa only [f, vectorCosetEquiv_smul, Equiv.apply_symm_apply] using hh
  · have hh := congrArg (fun q => (f q : V)) hgb
    simpa only [f, vectorCosetEquiv_smul, Equiv.apply_symm_apply] using hh

/-- The fifteen-point orbit size follows from the source hypotheses alone. -/
theorem vector_orbit_card_fifteen [Finite G]
    (ρ : Representation (ZMod 2) G V) (v : V)
    (hmodel : Nonempty (G ≃* PSL(4, ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (Set.range fun g => ρ g v)))
    (hquot : Nonempty (((vectorStabilizer ρ v) ⧸ pCore 2 (vectorStabilizer ρ v)) ≃*
      PSL(3, ZMod 2))) : Nat.card (Set.range fun g => ρ g v) = 15 := by
  rw [vector_orbit_card_eq_index] at hodd ⊢
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    exact (FifteenPointSubgroups.psl4_orders e _ hodd hquot).1
  · obtain ⟨e⟩ := hmodel
    exact (FifteenPointSubgroups.alternating7_orders e _ hodd hquot).1


open FifteenPointSubgroups
variable {K : Type*} [Group K]

private noncomputable def quotient_twoCore_map (e : G ≃* K) (H : Subgroup G) :
    (H ⧸ pCore 2 H) ≃* ((H.map e.toMonoidHom) ⧸ pCore 2 (H.map e.toMonoidHom)) :=
  QuotientGroup.congr _ _ (e.subgroupMap H) (pCore_map_iso 2 (e.subgroupMap H))

/-- Reduce an arbitrary marked subgroup to the two concrete action calculations. -/
theorem coset_action_of_models [Finite G]
    (hfour : ∀ H : Subgroup PSL(4, ZMod 2), H.index = 15 → Nat.card (pCore 2 H) = 8 →
      MulAction.IsMultiplyPretransitive PSL(4, ZMod 2) (PSL(4, ZMod 2) ⧸ H) 2)
    (hseven : ∀ H : Subgroup (alternatingGroup (Fin 7)),
      Nonempty (H ≃* PSL(3, ZMod 2)) →
      MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7))
        (alternatingGroup (Fin 7) ⧸ H) 2)
    (H : Subgroup G)
    (hmodel : Nonempty (G ≃* PSL(4, ZMod 2)) ∨ Nonempty (G ≃* alternatingGroup (Fin 7)))
    (hodd : Odd H.index)
    (hquot : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(3, ZMod 2))) :
    MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 ∧ H.index = 15 := by
  obtain ⟨f⟩ := hquot
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    let H' := H.map e.toMonoidHom
    have hidx : H.index = H'.index := Nat.card_congr (Subgroup.cosetEquivMap e H)
    have ho : Odd H'.index := hidx ▸ hodd
    have hq : Nonempty ((H' ⧸ pCore 2 H') ≃* PSL(3, ZMod 2)) :=
      ⟨(quotient_twoCore_map e H).symm.trans f⟩
    obtain ⟨hi, hc, _⟩ := psl4_orders (MulEquiv.refl _) H' ho hq
    refine ⟨Subgroup.two_pretransitive_of_map e H (hfour H' hi hc), ?_⟩
    exact hidx.trans hi
  · obtain ⟨e⟩ := hmodel
    let H' := H.map e.toMonoidHom
    have hidx : H.index = H'.index := Nat.card_congr (Subgroup.cosetEquivMap e H)
    have ho : Odd H'.index := hidx ▸ hodd
    have hq : Nonempty ((H' ⧸ pCore 2 H') ≃* PSL(3, ZMod 2)) :=
      ⟨(quotient_twoCore_map e H).symm.trans f⟩
    have heq := alternating7_equiv (MulEquiv.refl _) H' ho hq
    refine ⟨Subgroup.two_pretransitive_of_map e H (hseven H' heq), ?_⟩
    have hi := (alternating7_orders (MulEquiv.refl _) H' ho hq).1
    exact hidx.trans hi

universe u w

/-- Assemble the original orbit input after the two model action proofs. -/
theorem fifteenPointStabilizerInput_of_coset_actions
    (hfour : ∀ H : Subgroup PSL(4, ZMod 2), H.index = 15 → Nat.card (pCore 2 H) = 8 →
      MulAction.IsMultiplyPretransitive PSL(4, ZMod 2) (PSL(4, ZMod 2) ⧸ H) 2)
    (hseven : ∀ H : Subgroup (alternatingGroup (Fin 7)),
      Nonempty (H ≃* PSL(3, ZMod 2)) →
      MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7))
        (alternatingGroup (Fin 7) ⧸ H) 2) : FifteenPointStabilizerInput.{u,w} := by
  intro G V _ _ _ _ _ ρ v hmodel hodd hquot
  rw [vector_orbit_card_eq_index] at hodd
  obtain ⟨ht, hi⟩ := coset_action_of_models hfour hseven
    (vectorStabilizer ρ v) hmodel hodd hquot
  exact ⟨pairTransitiveOrbit_of_cosets ρ v ht, (vector_orbit_card_eq_index ρ v).trans hi⟩

/-- The source hypotheses give a twice-transitive orbit of size fifteen in the
original representation, without any spanning or finite-dimensionality premise. -/
theorem pairTransitiveOrbit_of_models [Finite G]
    (ρ : Representation (ZMod 2) G V) (v : V)
    (hmodel : Nonempty (G ≃* PSL(4, ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (Set.range fun g => ρ g v)))
    (hquot : Nonempty (((vectorStabilizer ρ v) ⧸ pCore 2 (vectorStabilizer ρ v)) ≃*
      PSL(3, ZMod 2))) :
    Representation.PairTransitiveOrbit ρ v ∧ Nat.card (Set.range fun g => ρ g v) = 15 := by
  rw [vector_orbit_card_eq_index] at hodd
  obtain ⟨ht, hi⟩ := FifteenPointSubgroups.coset_action
    (vectorStabilizer ρ v) hmodel hodd hquot
  exact ⟨pairTransitiveOrbit_of_cosets ρ v ht, (vector_orbit_card_eq_index ρ v).trans hi⟩

/-- Both concrete subgroup calculations discharge the full B.4.12(2) action input. -/
theorem fifteenPointStabilizerInput : FifteenPointStabilizerInput.{u,w} := by
  intro G V _ _ _ _ _ ρ v hmodel hodd hquot
  exact pairTransitiveOrbit_of_models ρ v hmodel hodd hquot

end CFSG.Quasithin.ChapterB.SmallRecognition
