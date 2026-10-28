module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Displacement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Constituents
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.QuadraticGeometry
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.BinaryOffender.SubspaceAction


/-!
# The opening local reductions in 15.3.58

We use the literal centralizer `H = C_G(Z)`, conjugate closure
`U = ⟨Z_S^H⟩`, and quotients `H* = H/O₂(H)` and `U/Z`.
The subgroup `V*` is the actual image of V, with a generator constructed
from its order two. No quotient centralizer is identified with the image
of an ambient centralizer.

The proof has three parts. First, relative normality of Y in YU gives
`O₂(Y) ≤ P`. The underlying coordinates of the two sums of s natural
binary planes in 15.3.54(4) make P/V trivial when s=0, contrary to
`V < O₂(Y)` from 15.3.9. This uses the multiplicity s in the printed
decomposition, not the unrelated cardinality exponent in the legacy
`Geometry.G26Witness.module_decomposition` field.

Second, any subgroup A with `Z ≤ A ≤ U` is the full preimage of its image
in U/Z. Consequently its quotient stabilizer has preimage `H ∩ N_G(A)`.
An actor centralizing V* preserves its displacement plane. The source
hyperplane `V ∩ U` has order eight, so cannot be totally singular in the
four-dimensional nondegenerate orthogonal space V. Thus 15.3.46(2)
places its normalizer in M, and 15.3.49(4–5) gives all three required
prime-to-three cardinalities.

Finally, the distinguished-line containment and the displacement identity
supply `hline`, while normalization by T of the order-two V* supplies
`hvT`, in `normalConstituentConclusion_of_source_fixed_line`.

These are conditional deductions from genuine earlier source facts. The
parent source-theorem assembly must supply:

* 15.3.9's strict core containment; 15.3.54(1), centrality in (2), and
  the actual quotient coordinates underlying (4); and U-normalization
  of Y (from normal Y in M and `U ≤ T ≤ M`).
* The actual nondegenerate four-dimensional orthogonal structure on V,
  and the singularity implication in 15.3.46(2).
* The action kernel and elementary quotient from 15.3.48, and the
  ambient prime-to-three statements in 15.3.49(4–5).
* The hyperplane order, order of V*, and displacement identity from
  15.3.53(2), along with `Z ≤ ZS ≤ V` and normalization of V by T.
* For the constituent conclusion: the paired fixed-line identity and
  dimension from 15.3.56, the preceding line sizes and commutator bound,
  and the constituent dimension hypothesis of 15.3.57(2).

`pair_denominator_normal` constructs the relative normality instance for
P/V from the centrality input. The coordinate isomorphism deliberately
forgets the Y-action: only the underlying direct sum is used here. These
results neither prove 15.3.54 nor complete the recognition in 15.3.58.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1123 and 1146–1149; 15.3.46–49 on printed pp.1141–1145.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
namespace LocalRestrictions
variable {G : Type*} [Group G]

/-- Relative normality of Y in YU, not ambient normality, places its two-core in P. -/
theorem coreY_le_pairP (Z ZS Y : Subgroup G) (g : G)
    (hI : pairI Z ZS g = Y ⊔ closureU Z ZS)
    (hUY : closureU Z ZS ≤ normalizer (Y : Set G)) :
    Stellmacher.twoCoreAmbient Y ≤ pairP Z ZS g := by
  change Y.pCoreIn 2 ≤ (pairI Z ZS g).pCoreIn 2
  apply pCoreIn_mono_of_normalizes
  · rw [hI]; exact le_sup_left
  · rw [hI]; exact sup_le Y.le_normalizer hUY

/-- The underlying coordinates of the two sums of s natural binary planes
in 15.3.54(4) rule out s=0 by 15.3.9. -/
theorem positive_of_source_decomposition (Z ZS V Y : Subgroup G) (g : G) (s : ℕ)
    [(V.subgroupOf (pairP Z ZS g)).Normal]
    (hI : pairI Z ZS g = Y ⊔ closureU Z ZS)
    (hUY : closureU Z ZS ≤ normalizer (Y : Set G))
    (hV : V < Stellmacher.twoCoreAmbient Y)
    (hdecomp : Nonempty ((pairP Z ZS g ⧸ V.subgroupOf (pairP Z ZS g)) ≃*
      (Fin 2 → Fin s → Multiplicative (Fin 2 → ZMod 2)))) : 0 < s := by
  obtain ⟨e⟩ := hdecomp
  by_contra hs
  have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
  subst s
  have hPV : pairP Z ZS g ≤ V := by
    intro x hx
    have he : (QuotientGroup.mk' (V.subgroupOf (pairP Z ZS g)) ⟨x, hx⟩) = 1 :=
      e.injective (Subsingleton.elim _ _)
    exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : pairP Z ZS g)).mp he
  exact (not_le_of_gt hV) ((coreY_le_pairP Z ZS Y g hI hUY).trans hPV)

/-- All containments V < O₂(Y) ≤ P use the relative normality proved above. -/
theorem V_lt_pairP (Z ZS V Y : Subgroup G) (g : G)
    (hI : pairI Z ZS g = Y ⊔ closureU Z ZS)
    (hUY : closureU Z ZS ≤ normalizer (Y : Set G))
    (hV : V < Stellmacher.twoCoreAmbient Y) : V < pairP Z ZS g :=
  lt_of_lt_of_le hV (coreY_le_pairP Z ZS Y g hI hUY)

/-- The centrality clause of 15.3.54(2) supplies the relative normality
needed for the literal quotient P/V. -/
theorem pair_denominator_normal (Z ZS V : Subgroup G) (g : G)
    (hcentral : V ≤ centralizer (pairP Z ZS g : Set G)) :
    (V.subgroupOf (pairP Z ZS g)).Normal := by
  constructor
  intro v hv p
  change (v : G) ∈ V at hv
  change (p : G) * (v : G) * (p : G)⁻¹ ∈ V
  have hc := mem_centralizer_iff.mp (hcentral hv) p p.property
  simpa only [hc, mul_inv_cancel_right] using hv

private theorem normalizer_le_centralizer_of_card_two
    (A : Subgroup G) (hA : Nat.card A = 2) :
    normalizer (A : Set G) ≤ centralizer (A : Set G) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hyne : yA ≠ 1 := by
    intro hy
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have h := congrArg (fun a : G => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using h
  have heq : yA = xA := (hzuniq yA hyne).trans (hzuniq xA (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
  have h := congrArg (fun a : G => a * g) heq'
  simpa [mul_assoc] using h.symm

variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The linear subspace with the actual image subgroup as underlying set. -/
noncomputable def vectorSubspace (A : Subgroup G) : Submodule (ZMod 2) (Space Z ZS) :=
  AddSubgroup.toZModSubmodule 2 (vectorImage Z ZS A).toAddSubgroup

omit [IsElementaryAbelian 2 (VectorQuotient Z ZS)] in
/-- A subgroup containing Z is the full preimage of its image in U/Z. -/
theorem vectorImage_preimage (A : Subgroup G) (hZA : Z ≤ A) :
    (vectorImage Z ZS A).comap (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))) =
      A.subgroupOf (closureU Z ZS) := by
  apply comap_map_eq_self
  rw [QuotientGroup.ker_mk']
  exact fun _ hx => hZA hx

private theorem mem_vectorSubspace_mk (A : Subgroup G) (hZA : Z ≤ A)
    (u : closureU Z ZS) :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) ∈
      vectorSubspace Z ZS A ↔ (u : G) ∈ A := by
  change u ∈ (vectorImage Z ZS A).comap (QuotientGroup.mk' _) ↔ _
  rw [vectorImage_preimage Z ZS A hZA]
  rfl

open Representation.BinaryOffender

/-- The preimage in H of the setwise quotient stabilizer is precisely the
relative ambient normalizer. No centralizer-image assertion is used. -/
theorem stabilizer_preimage
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (A : Subgroup G) (hZA : Z ≤ A) (hAU : A ≤ closureU Z ZS) :
    (subspaceStabilizer (actorRepresentation Z ZS hkernel) (vectorSubspace Z ZS A)).comap
      (QuotientGroup.mk' (pCore 2 (centralizerH Z))) =
      (normalizer (A : Set G)).subgroupOf (centralizerH Z) := by
  ext h
  change (∀ w, actorRepresentation Z ZS hkernel (QuotientGroup.mk' _ h) w ∈
    vectorSubspace Z ZS A ↔ w ∈ vectorSubspace Z ZS A) ↔
      (h : G) ∈ normalizer (A : Set G)
  have hU := H_normalizes_closureU Z ZS h.property
  have hconj (u : closureU Z ZS) :
      actorRepresentation Z ZS hkernel (QuotientGroup.mk' _ h)
        (Additive.ofMul (QuotientGroup.mk' _ u)) ∈ vectorSubspace Z ZS A ↔
          (h : G) * (u : G) * (h : G)⁻¹ ∈ A := by
    rw [actorRepresentation_mk]
    change Additive.ofMul (quotientAction Z ZS h (QuotientGroup.mk' _ u)) ∈ _ ↔ _
    rw [quotientAction_mk]
    exact mem_vectorSubspace_mk Z ZS A hZA _
  constructor
  · intro hs
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact (hconj ⟨x, hAU hx⟩).mp ((hs _).mpr
        ((mem_vectorSubspace_mk Z ZS A hZA _).mpr hx))
    · intro hx
      have hxU := (mem_normalizer_iff.mp hU x).mpr (hAU hx)
      exact (mem_vectorSubspace_mk Z ZS A hZA ⟨x, hxU⟩).mp
        ((hs _).mp ((hconj ⟨x, hxU⟩).mpr hx))
  · intro hn w
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w.toMul
    have hw : w = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
    rw [hw, hconj, mem_vectorSubspace_mk Z ZS A hZA]
    exact (mem_normalizer_iff.mp hn u).symm

/-- Equivalently, the stabilizer is the quotient image of that relative
normalizer, with the full preimage established first. -/
theorem stabilizer_eq_actorImage_normalizer
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (A : Subgroup G) (hZA : Z ≤ A) (hAU : A ≤ closureU Z ZS) :
    subspaceStabilizer (actorRepresentation Z ZS hkernel) (vectorSubspace Z ZS A) =
      actorImage Z (normalizer (A : Set G)) := by
  rw [actorImage, ← stabilizer_preimage Z ZS hkernel A hZA hAU]
  symm
  apply map_comap_eq_self
  rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact le_top

/-- Centralizing the marked actor preserves the literal displacement space. -/
theorem centralizer_le_displacement_stabilizer
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (v : ActorQuotient Z) :
    centralizer (zpowers v : Set (ActorQuotient Z)) ≤
      subspaceStabilizer (actorRepresentation Z ZS hkernel)
        (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) := by
  apply le_subspaceStabilizer
  intro a ha w hw
  obtain ⟨x, rfl⟩ := hw
  refine ⟨actorRepresentation Z ZS hkernel a x, ?_⟩
  change actorRepresentation Z ZS hkernel v (actorRepresentation Z ZS hkernel a x) -
    actorRepresentation Z ZS hkernel a x =
    actorRepresentation Z ZS hkernel a (actorRepresentation Z ZS hkernel v x - x)
  rw [map_sub]
  have he := congrArg (fun b => actorRepresentation Z ZS hkernel b x)
    (mem_centralizer_iff.mp ha v (mem_zpowers v))
  simpa only [map_mul, Module.End.mul_apply] using
    congrArg (fun y => y - actorRepresentation Z ZS hkernel a x) he



/-- Fixing a subspace pointwise implies stabilizing it setwise. -/
theorem pointwise_le_stabilizer
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (D : Submodule (ZMod 2) (Space Z ZS)) :
    subspaceKernel (actorRepresentation Z ZS hkernel) D ⊤ ≤
      subspaceStabilizer (actorRepresentation Z ZS hkernel) D := by
  apply le_subspaceStabilizer
  intro a ha w hw
  rw [ha.2 w hw]
  exact hw

/-- In particular the pointwise line fixer lifts to the normalizer of ZS,
not to an unjustified ambient pointwise centralizer. -/
theorem line_fixer_preimage_le
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZZS : Z ≤ ZS) :
    (subspaceKernel (actorRepresentation Z ZS hkernel) (vectorSubspace Z ZS ZS) ⊤).comap
      (QuotientGroup.mk' (pCore 2 (centralizerH Z))) ≤
      (normalizer (ZS : Set G)).subgroupOf (centralizerH Z) := by
  rw [← stabilizer_preimage Z ZS hkernel ZS hZZS (ZS_le_closureU Z ZS)]
  exact comap_mono (pointwise_le_stabilizer Z ZS hkernel _)

omit [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- Quotient image order divides the order of its genuine relative preimage. -/
theorem card_actorImage_dvd (A : Subgroup G) :
    Nat.card (actorImage Z A) ∣ Nat.card (A ⊓ centralizerH Z : Subgroup G) := by
  have hc : Nat.card (A.subgroupOf (centralizerH Z)) =
      Nat.card (A ⊓ centralizerH Z : Subgroup G) := by
    rw [← inf_subgroupOf_right A (centralizerH Z)]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  exact hc ▸ (A.subgroupOf (centralizerH Z)).card_map_dvd
    (QuotientGroup.mk' (pCore 2 (centralizerH Z)))

/-- The lifted stabilizer of the actual displacement plane normalizes V∩U. -/
theorem displacement_stabilizer_preimage
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V : Subgroup G) (v : ActorQuotient Z)
    (hZV : Z ≤ V) (hZZS : Z ≤ ZS)
    (hdisp : LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) =
      vectorSubspace Z ZS (V ⊓ closureU Z ZS)) :
    (subspaceStabilizer (actorRepresentation Z ZS hkernel)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id))).comap
        (QuotientGroup.mk' (pCore 2 (centralizerH Z))) =
      (normalizer (V ⊓ closureU Z ZS : Set G)).subgroupOf (centralizerH Z) := by
  rw [hdisp]
  exact stabilizer_preimage Z ZS hkernel _
    (le_inf hZV (hZZS.trans (ZS_le_closureU Z ZS))) inf_le_right

/-- The source centralizer inclusion C_H*(V*) ≤ M_H* follows by preserving
the displacement plane and lifting its stabilizer. -/
theorem centralizer_le_actorImage_M
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V M : Subgroup G) (v : ActorQuotient Z)
    (hZV : Z ≤ V) (hZZS : Z ≤ ZS)
    (hdisp : LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) =
      vectorSubspace Z ZS (V ⊓ closureU Z ZS))
    (hcontrol : normalizer (V ⊓ closureU Z ZS : Set G) ≤ M) :
    centralizer (zpowers v : Set (ActorQuotient Z)) ≤ actorImage Z M := by
  apply (centralizer_le_displacement_stabilizer Z ZS hkernel v).trans
  rw [hdisp, stabilizer_eq_actorImage_normalizer Z ZS hkernel _
    (le_inf hZV (hZZS.trans (ZS_le_closureU Z ZS))) inf_le_right]
  exact map_mono (fun _ hx => hcontrol hx)

/-- The three prime-to-three restrictions used at the start of 15.3.58,
from 15.3.46(2), 15.3.49(4–5), and the earlier displacement identity. -/
theorem three_prime_restrictions [Finite G]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V M : Subgroup G) (v : ActorQuotient Z)
    (hZV : Z ≤ V) (hZZS : Z ≤ ZS)
    (hdisp : LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) =
      vectorSubspace Z ZS (V ⊓ closureU Z ZS))
    (hcontrol : normalizer (V ⊓ closureU Z ZS : Set G) ≤ M)
    (h49four : Nat.Coprime 3 (Nat.card (M ⊓ centralizerH Z : Subgroup G)))
    (h49five : Nat.Coprime 3 (Nat.card (normalizer (ZS : Set G)))) :
    Nat.Coprime 3 (Nat.card (subspaceStabilizer (actorRepresentation Z ZS hkernel)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)))) ∧
    Nat.Coprime 3 (Nat.card (subspaceKernel (actorRepresentation Z ZS hkernel)
      (vectorSubspace Z ZS ZS) ⊤)) ∧
    Nat.Coprime 3 (Nat.card (centralizer (zpowers v : Set (ActorQuotient Z)))) := by
  have hplane : subspaceStabilizer (actorRepresentation Z ZS hkernel)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) ≤
        actorImage Z M := by
    rw [hdisp, stabilizer_eq_actorImage_normalizer Z ZS hkernel _
      (le_inf hZV (hZZS.trans (ZS_le_closureU Z ZS))) inf_le_right]
    exact map_mono (fun _ hx => hcontrol hx)
  have hMc := h49four.of_dvd_right (card_actorImage_dvd Z M)
  have hp := hMc.of_dvd_right (card_dvd_of_le hplane)
  refine ⟨hp, ?_, hp.of_dvd_right
    (card_dvd_of_le (centralizer_le_displacement_stabilizer Z ZS hkernel v))⟩
  have hline := pointwise_le_stabilizer Z ZS hkernel (vectorSubspace Z ZS ZS)
  rw [stabilizer_eq_actorImage_normalizer Z ZS hkernel ZS hZZS (ZS_le_closureU Z ZS)] at hline
  exact h49five.of_dvd_right ((card_dvd_of_le hline).trans
    ((card_actorImage_dvd Z (normalizer (ZS : Set G))).trans (card_dvd_of_le inf_le_left)))

/-- The distinguished line lies in the actual displacement plane, by the
ambient line containment and the displacement identity in 15.3.53(2). -/
theorem distinguishedLine_le_displacement
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V : Subgroup G) (v : ActorQuotient Z) (hZSV : ZS ≤ V)
    (hdisp : LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) =
      vectorSubspace Z ZS (V ⊓ closureU Z ZS)) :
    ∀ w : Space Z ZS, w.toMul ∈ distinguishedLine Z ZS →
      w ∈ LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) := by
  intro w hw
  rw [hdisp]
  change w.toMul ∈ vectorImage Z ZS (V ⊓ closureU Z ZS)
  exact (map_mono (show ZS.subgroupOf (closureU Z ZS) ≤
    (V ⊓ closureU Z ZS).subgroupOf (closureU Z ZS) from
      fun u hu => ⟨hZSV hu, u.property⟩)) hw



omit [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- The order-two conclusion of 15.3.53 supplies an actual marked generator. -/
theorem exists_marked_generator (V : Subgroup G)
    (hVstar : Nat.card (actorImage Z V) = 2) :
    ∃ v : ActorQuotient Z, v ≠ 1 ∧ zpowers v = actorImage Z V := by
  obtain ⟨v, hv, huniq⟩ := (Nat.card_eq_two_iff' (1 : actorImage Z V)).mp hVstar
  refine ⟨v, fun he => hv (Subtype.ext he), le_antisymm ?_ ?_⟩
  · exact zpowers_le.mpr v.property
  · intro x hx
    by_cases he : x = 1
    · exact he ▸ (zpowers (v : ActorQuotient Z)).one_mem
    · have hxe : (⟨x, hx⟩ : actorImage Z V) = v :=
        huniq ⟨x, hx⟩ (fun hh => he (congrArg Subtype.val hh))
      rw [show x = (v : ActorQuotient Z) from congrArg Subtype.val hxe]
      exact mem_zpowers v.val

omit [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- Normalization by T makes its image centralize the order-two V*.
Both subgroup images are taken through the literal H/O₂(H) map. -/
theorem actorImage_T_le_centralizer_V (V T : Subgroup G)
    (hVH : V ≤ centralizerH Z)
    (hTV : T ≤ normalizer (V : Set G))
    (hVstar : Nat.card (actorImage Z V) = 2) :
    actorImage Z T ≤ centralizer (actorImage Z V : Set (ActorQuotient Z)) := by
  apply le_trans _ (normalizer_le_centralizer_of_card_two _ hVstar)
  apply le_trans _ ((V.subgroupOf (centralizerH Z)).le_normalizer_map
    (QuotientGroup.mk' (pCore 2 (centralizerH Z))))
  apply map_mono
  rw [← subgroupOf_normalizer_eq hVH]
  exact fun _ hx => hTV hx

omit [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- The marked generator of V* commutes with every element of T*. -/
theorem marked_commutes_actorImage_T (V T : Subgroup G) (v : ActorQuotient Z)
    (hVH : V ≤ centralizerH Z)
    (hTV : T ≤ normalizer (V : Set G))
    (hVstar : Nat.card (actorImage Z V) = 2)
    (hmark : zpowers v = actorImage Z V) :
    ∀ t : actorImage Z T, Commute v (t : ActorQuotient Z) := by
  intro t
  exact mem_centralizer_iff.mp
    (actorImage_T_le_centralizer_V Z V T hVH hTV hVstar t.property) v
      (hmark ▸ mem_zpowers v)

/-- The constituent theorem with its two formerly external inputs discharged
from the actual marked V*, normalization, and displacement identity. -/
theorem normalConstituentConclusion_of_marked_source [Finite G]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4)
    (hcommZS : ⁅ZS, (T : Subgroup G)⁆ ≤ Z)
    (J : Subgroup (centralizerH Z))
    (hJT : J ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hJ : letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
      FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS)
    (V : Subgroup G) (hVH : V ≤ centralizerH Z)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hVstar : Nat.card (actorImage Z V) = 2)
    (hZSV : ZS ≤ V)
    (K : Subgroup (ActorQuotient Z)) [K.Normal] (v : ActorQuotient Z) (s : ℕ)
    (hmark : zpowers v = actorImage Z V)
    (hdisp : LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) =
      vectorSubspace Z ZS (V ⊓ closureU Z ZS))
    (hsmall : ∀ A : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype),
      A.toRepresentation.IsIrreducible → 3 ≤ Module.finrank (ZMod 2) A.toSubmodule)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) (Space Z ZS) = 2 * (s + 2)) :
    NormalConstituentConclusion (actorRepresentation Z ZS hkernel) K v s := by
  exact normalConstituentConclusion_of_source_fixed_line Z ZS hkernel T hTH
    hZZS hZ hZS hcommZS J hJT hJ K v s
    (marked_commutes_actorImage_T Z V T v hVH hTV hVstar hmark)
    (distinguishedLine_le_displacement Z ZS hkernel V v hZSV hdisp) hsmall hrank hdim



omit [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- 15.3.46(2) controls the normalizer of the source hyperplane: its order
is eight by 15.3.53(2), whereas a totally singular subgroup has order at
most four in the nondegenerate four-dimensional space V. -/
theorem normalizer_control_of_source [Finite G]
    (V M : Subgroup G) [IsElementaryAbelian 2 V]
    (Q : QuadraticForm (ZMod 2) (Additive V))
    (hQ : Q.polarBilin.Nondegenerate)
    (hdimV : Module.finrank (ZMod 2) (Additive V) = 4)
    (h46 : ∀ A : Subgroup G, ⊥ < A → A < V →
      ¬ normalizer (A : Set G) ≤ M → FusionCore.IsTotallySingular Q A)
    (h53 : Nat.card (V ⊓ closureU Z ZS : Subgroup G) = 8) :
    normalizer (V ⊓ closureU Z ZS : Set G) ≤ M := by
  have hVcard : Nat.card V = 16 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, hdimV] at hc
    exact hc
  have hbot : ⊥ < V ⊓ closureU Z ZS := by
    apply lt_of_le_of_ne bot_le
    intro he
    have hc := h53
    rw [← he, Subgroup.card_bot] at hc
    omega
  have hlt : V ⊓ closureU Z ZS < V := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    rw [he, hVcard] at h53
    omega
  by_contra hn
  have hsmall := FusionCore.card_le_four_of_totallySingular Q hQ hdimV
    inf_le_left (h46 _ hbot hlt hn)
  omega

/-- The actual restrictions on H*=H/O₂(H), with normalizer control derived
from the source singularity statement rather than included as an assumption.
The marked cyclic subgroup is identified with the actual image V*. -/
theorem three_prime_restrictions_of_source [Finite G]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V M : Subgroup G) [IsElementaryAbelian 2 V]
    (Q : QuadraticForm (ZMod 2) (Additive V))
    (hQ : Q.polarBilin.Nondegenerate)
    (hdimV : Module.finrank (ZMod 2) (Additive V) = 4)
    (h46 : ∀ A : Subgroup G, ⊥ < A → A < V →
      ¬ normalizer (A : Set G) ≤ M → FusionCore.IsTotallySingular Q A)
    (h53 : Nat.card (V ⊓ closureU Z ZS : Subgroup G) = 8)
    (v : ActorQuotient Z) (hmark : zpowers v = actorImage Z V)
    (hZSV : ZS ≤ V) (hZZS : Z ≤ ZS)
    (hdisp : LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) =
      vectorSubspace Z ZS (V ⊓ closureU Z ZS))
    (h49four : Nat.Coprime 3 (Nat.card (M ⊓ centralizerH Z : Subgroup G)))
    (h49five : Nat.Coprime 3 (Nat.card (normalizer (ZS : Set G)))) :
    centralizer (actorImage Z V : Set (ActorQuotient Z)) ≤ actorImage Z M ∧
    Nat.Coprime 3 (Nat.card (subspaceStabilizer (actorRepresentation Z ZS hkernel)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)))) ∧
    Nat.Coprime 3 (Nat.card (subspaceKernel (actorRepresentation Z ZS hkernel)
      (vectorSubspace Z ZS ZS) ⊤)) ∧
    Nat.Coprime 3 (Nat.card (centralizer (actorImage Z V : Set (ActorQuotient Z)))) := by
  have hcontrol := normalizer_control_of_source Z ZS V M Q hQ hdimV h46 h53
  rw [← hmark]
  exact ⟨centralizer_le_actorImage_M Z ZS hkernel V M v (hZZS.trans hZSV) hZZS
    hdisp hcontrol, three_prime_restrictions Z ZS hkernel V M v
      (hZZS.trans hZSV) hZZS hdisp hcontrol h49four h49five⟩

end LocalRestrictions
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
