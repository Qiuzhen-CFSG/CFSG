module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Assembly
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalModel
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# Faithful marked transport for the two endpoint normalizers

Let E be either elementary-eight endpoint core. Its self-centralization
identifies the kernel of N_G(E)'s conjugation action with the literal embedded
E. The quotient and Aut(E) both have order 168, so the induced action is an
isomorphism. Binary vector-space coordinates on E, followed by the inverse
of the faithful natural SL₃(2) action, therefore give compatible quotient
and module coordinates. The supplied complement constructs `SplitNaturalData`;
its block isomorphism preserves the original quotient projection and takes
the embedded E to the translation kernel.

Apply the explicit `ModelGeometry` premise to the image of the actual A in
each block. Normalizers and intersections transport along the block
isomorphism and then along the ambient subgroup inclusion. This gives both
overlap orders, both order-four planes, and the literal plane-stabilizer
equalities needed by `configuration_parabolics_of_overlap_card`. We import
Assembly, independently of that later parabolic assembly, to avoid a cycle.
The concrete model calculation is still a premise: its producer is
`qt-i46-nonnormal-a3-split-model`, and the parabolics assembly owner must supply it.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 3.1–3.2, printed pp.36–37,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

public section

open Subgroup
open Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
open scoped IsMulCommutative

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics.MarkedTransport

private theorem eight_coordinates (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 8) : Nonempty (E ≃* E3) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
    have hs := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hs
    simpa only [Nat.card_zmod, hc, show (2 : ℕ) ^ 3 = 8 by decide] using hs.symm
  have hd : Module.finrank (ZMod 2) (Additive E) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hd).equivFun.toAddEquiv.toMultiplicativeRight⟩

private theorem action_bijective : Function.Bijective naturalAction := by
  have hi : Function.Injective naturalAction := by
    intro a b hab
    apply Matrix.SpecialLinearGroup.toLin'_injective
    ext v : 1
    exact congrArg (fun f : MulAut E3 => (f (Multiplicative.ofAdd v)).toAdd) hab
  have : IsElementaryAbelian 2 E3 := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      funext i
      change v.toAdd i + v.toAdd i = 0
      exact CharTwo.add_self_eq_zero _) }
  apply (Nat.bijective_iff_injective_and_card naturalAction).mpr
  refine ⟨hi, ?_⟩
  rw [card_SL, card_mulAut_of_elementary_eight E3 (by simp [Nat.card_eq_fintype_card])]

private noncomputable def actionEquiv : SL ≃* MulAut E3 :=
  MulEquiv.ofBijective naturalAction action_bijective

variable {G : Type*} [Group G] [Finite G]

private noncomputable def conjugationQuotient (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 8)
    (hself : centralizer (E : Set G) = E)
    (hq : Nat.card (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G))) = 168) :
    (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G))) ≃* MulAut E := by
  have hk : E.subgroupOf (normalizer (E : Set G)) = E.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker, hself]
  let f := QuotientGroup.lift _ E.normalizerMonoidHom hk.le
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨(QuotientGroup.injective_lift_iff _ _ _).mpr hk,
      hq.trans (card_mulAut_of_elementary_eight E hc).symm⟩)

private noncomputable def normalizerSplitData (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 8)
    (hself : centralizer (E : Set G) = E)
    (hq : Nat.card (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G))) = 168)
    (hs : ∃ K : Subgroup (normalizer (E : Set G)),
      (E.subgroupOf (normalizer (E : Set G))).IsComplement' K) :
    SplitNaturalData (E.subgroupOf (normalizer (E : Set G))) := by
  let e := (eight_coordinates E hc).some
  let q := conjugationQuotient E hc hself hq
  refine {
    quotient := q.trans ((MulAut.congr e).trans actionEquiv.symm)
    moduleEquiv := (subgroupOfEquivOfLe E.le_normalizer).trans e
    complement := hs.choose
    splitting := hs.choose_spec
    equivariant := ?_ }
  intro n v
  change e (E.normalizerMonoidHom n ((subgroupOfEquivOfLe E.le_normalizer) v)) =
    naturalAction (actionEquiv.symm ((MulAut.congr e) (q (QuotientGroup.mk' _ n))))
      (e ((subgroupOfEquivOfLe E.le_normalizer) v))
  change _ = actionEquiv (actionEquiv.symm _) _
  rw [MulEquiv.apply_symm_apply]
  change _ = (MulAut.congr e) (E.normalizerMonoidHom n) _
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem splitData_core_map {L : Type*} [Group L] {V : Subgroup L} [V.Normal]
    (s : SplitNaturalData V) : V.map s.blockEquiv.toMonoidHom = projection.ker := by
  ext b
  obtain ⟨x, rfl⟩ := s.blockEquiv.surjective b
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, MonoidHom.mem_ker,
    s.blockEquiv_projection, MulEquiv.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff x).symm

omit [Finite G] in
private theorem split_overlap (E A : Subgroup G)
    (s : SplitNaturalData (E.subgroupOf (normalizer (E : Set G))))
    (hA : A ≤ normalizer (E : Set G)) [IsElementaryAbelian 2 A]
    (hAc : Nat.card A = 16)
    (model : ∀ B : Subgroup Block, IsElementaryAbelian 2 B → Nat.card B = 16 →
      Nat.card (normalizer (B : Set Block)) = 192 ∧
      Nat.card (B ⊓ projection.ker : Subgroup Block) = 4 ∧
      normalizer (B : Set Block) = normalizer ((B ⊓ projection.ker : Subgroup Block) : Set Block)) :
    Nat.card (normalizer (E : Set G) ⊓ normalizer (A : Set G) : Subgroup G) = 192 ∧
    Nat.card (A ⊓ E : Subgroup G) = 4 ∧
    normalizer (E : Set G) ⊓ normalizer (A : Set G) =
      normalizer (E : Set G) ⊓ normalizer ((A ⊓ E : Subgroup G) : Set G) := by
  let N := normalizer (E : Set G)
  let A' := A.subgroupOf N
  let V := E.subgroupOf N
  let e := s.blockEquiv
  let B := A'.map e.toMonoidHom
  have : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hA
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hBc : Nat.card B = 16 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv, hAc]
  obtain ⟨hc, hp, hn⟩ := model B hB hBc
  have hplane : (A' ⊓ V).map e.toMonoidHom = B ⊓ projection.ker := by
    rw [map_inf _ _ _ e.injective, splitData_core_map]
  have hnc : Nat.card (normalizer (A' : Set N)) = 192 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective (K := normalizer (A' : Set N)),
      map_normalizer_eq_of_bijective _ e.bijective]
    exact hc
  have hpc : Nat.card (A' ⊓ V : Subgroup N) = 4 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective (K := A' ⊓ V), hplane]
    exact hp
  have hn' : normalizer (A' : Set N) = normalizer ((A' ⊓ V : Subgroup N) : Set N) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_normalizer_eq_of_bijective _ e.bijective,
      map_normalizer_eq_of_bijective _ e.bijective, hplane]
    exact hn
  have hN : (normalizer (A' : Set N)).map N.subtype = N ⊓ normalizer (A : Set G) := by
    rw [← subgroupOf_normalizer_eq hA, subgroupOf_map_subtype, inf_comm]
  have hI : (A' ⊓ V).map N.subtype = A ⊓ E := by
    rw [map_inf _ _ _ N.subtype_injective, map_subgroupOf_eq_of_le hA,
      map_subgroupOf_eq_of_le E.le_normalizer]
  have hNP : (normalizer ((A' ⊓ V : Subgroup N) : Set N)).map N.subtype =
      N ⊓ normalizer ((A ⊓ E : Subgroup G) : Set G) := by
    change (normalizer ((A ⊓ E).subgroupOf N : Set N)).map N.subtype = _
    rw [← subgroupOf_normalizer_eq (inf_le_left.trans hA), subgroupOf_map_subtype, inf_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hN, card_map_of_injective N.subtype_injective, hnc]
  · rw [← hI, card_map_of_injective N.subtype_injective, hpc]
  · rw [← hN, ← hNP, hn']

variable {z g : G}

/-- The actual point normalizer as a split natural extension, with the
quotient identification induced by its faithful conjugation action. -/
noncomputable def pointData (d : IntersectionData z g) (c : A3Configuration z g) :
    SplitNaturalData ((coreIntersection z g).subgroupOf
      (normalizer (coreIntersection z g : Set G))) := by
  letI := d.elementary
  exact normalizerSplitData _ d.card d.self_centralizing
    ((Nat.card_congr d.normalizer_quotient.some.toEquiv).trans card_PSL) c.point_split

/-- The same action-compatible construction for the second endpoint. -/
noncomputable def planeData (c : A3Configuration z g) (dy : IntersectionData z c.y) :
    SplitNaturalData ((coreIntersection z c.y).subgroupOf
      (normalizer (coreIntersection z c.y : Set G))) := by
  letI := dy.elementary
  exact normalizerSplitData _ dy.card dy.self_centralizing
    ((Nat.card_congr dy.normalizer_quotient.some.toEquiv).trans card_PSL) c.plane_split

omit [Finite G] in
/-- The middle elementary sixteen lies in the literal point normalizer. -/
theorem A_le_point (d : IntersectionData z g) (c : A3Configuration z g) :
    c.A ≤ normalizer (coreIntersection z g : Set G) :=
  c.A_le_sylow.trans ((map_subtype_le _).trans (intersection_centralizer_le_normalizer d))

omit [Finite G] in
/-- The middle elementary sixteen lies in the literal plane normalizer. -/
theorem A_le_plane (c : A3Configuration z g) (dy : IntersectionData z c.y) :
    c.A ≤ normalizer (coreIntersection z c.y : Set G) :=
  c.A_le_sylow.trans ((map_subtype_le _).trans (intersection_centralizer_le_normalizer dy))

/-- The concrete split-model calculation supplied by the separate model
producer. This remains an explicit premise of the source assembly. -/
abbrev ModelGeometry : Prop :=
  ∀ B : Subgroup Block, IsElementaryAbelian 2 B → Nat.card B = 16 →
    Nat.card (normalizer (B : Set Block)) = 192 ∧
    Nat.card (B ⊓ projection.ker : Subgroup Block) = 4 ∧
    normalizer (B : Set Block) = normalizer ((B ⊓ projection.ker : Subgroup Block) : Set Block)

/-- The point overlap has order 192 and is exactly the stabilizer of the
actual order-four intersection with the point core. -/
theorem point_geometry (d : IntersectionData z g) (c : A3Configuration z g)
    (model : ModelGeometry) :
    Nat.card (normalizer (coreIntersection z g : Set G) ⊓ normalizer (c.A : Set G) : Subgroup G) = 192 ∧
    Nat.card (c.A ⊓ coreIntersection z g : Subgroup G) = 4 ∧
    normalizer (coreIntersection z g : Set G) ⊓ normalizer (c.A : Set G) =
      normalizer (coreIntersection z g : Set G) ⊓
        normalizer ((c.A ⊓ coreIntersection z g : Subgroup G) : Set G) := by
  have := c.elementary
  exact split_overlap _ _ (pointData d c) (A_le_point d c) c.card model

/-- The analogous three conclusions at the second endpoint. -/
theorem plane_geometry (c : A3Configuration z g) (dy : IntersectionData z c.y)
    (model : ModelGeometry) :
    Nat.card (normalizer (coreIntersection z c.y : Set G) ⊓ normalizer (c.A : Set G) : Subgroup G) = 192 ∧
    Nat.card (c.A ⊓ coreIntersection z c.y : Subgroup G) = 4 ∧
    normalizer (coreIntersection z c.y : Set G) ⊓ normalizer (c.A : Set G) =
      normalizer (coreIntersection z c.y : Set G) ⊓
        normalizer ((c.A ⊓ coreIntersection z c.y : Subgroup G) : Set G) := by
  have := c.elementary
  exact split_overlap _ _ (planeData c dy) (A_le_plane c dy) c.card model

/-- The point block isomorphism carries the actual embedded core to the
kernel of the split-model projection. -/
theorem point_core_map (d : IntersectionData z g) (c : A3Configuration z g) :
    ((coreIntersection z g).subgroupOf
      (normalizer (coreIntersection z g : Set G))).map
        (pointData d c).blockEquiv.toMonoidHom = projection.ker :=
  splitData_core_map (pointData d c)

/-- The second endpoint block isomorphism has the same exact core marking. -/
theorem plane_core_map (c : A3Configuration z g) (dy : IntersectionData z c.y) :
    ((coreIntersection z c.y).subgroupOf
      (normalizer (coreIntersection z c.y : Set G))).map
        (planeData c dy).blockEquiv.toMonoidHom = projection.ker :=
  splitData_core_map (planeData c dy)

/-- The two literal cardinalities consumed by the parabolic assembly. -/
theorem endpoint_overlap_cards (d : IntersectionData z g)
    (c : A3Configuration z g) (dy : IntersectionData z c.y) (model : ModelGeometry) :
    Nat.card (normalizer (coreIntersection z g : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192 ∧
    Nat.card (normalizer (coreIntersection z c.y : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192 :=
  ⟨(point_geometry d c model).1, (plane_geometry c dy model).1⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics.MarkedTransport

end
