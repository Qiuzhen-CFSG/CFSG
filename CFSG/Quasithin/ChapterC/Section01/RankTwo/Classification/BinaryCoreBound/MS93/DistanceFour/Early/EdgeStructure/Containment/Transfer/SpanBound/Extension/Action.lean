module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Cocycle
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Extension.Groups
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SpanAction.Basic

/-!
# Conjugation on the literal neighboring extension quotient

The action of the local stabilizer on H/D_alpha factors through its actual
SL3(2) quotient using the kernel bound proved in `Groups`. We construct this
action and its binary linearization. The subrepresentation `Action.natural`
is the image of the literal Z_alpha; its preimage is U_alpha D_alpha by the
source decomposition of Z_alpha.

For unequal neighboring kernels, the image of Q_delta in SL3(2) is a
nontrivial two-group. Cauchy's theorem supplies an involution in this image,
which fixes every neighboring displacement vector. This does not require
an involution lifting outside Q_alpha.

`Action.HasNaturalMarking` records the remaining marking obligation; it has
no constructor here. The trivial-quotient and fixed-space calculations also
remain separate before the cocycle calculation can be applied.

Source: Meierfrankenfeld--Stellmacher (1993), (4.2)(i), printed p.882.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound.Extension
variable {G : Type*} [Group G]

private theorem conjugation_denominator (S H D : Subgroup G)
    (hH : S ≤ normalizer H) (hD : S ≤ normalizer D) (hDH : D ≤ H) (g : S) :
    (D.subgroupOf H).map (Offenders.conjugation S H hH g).toMonoidHom = D.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le hDH]
  have he : H.subtype.comp (Offenders.conjugation S H hH g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := rfl
  rw [he, ← map_map, map_subgroupOf_eq_of_le hDH]
  exact mem_normalizer_iff_map_conj_eq.mp (hD g.property)

private noncomputable def quotientConjugation (S H D : Subgroup G)
    (hH : S ≤ normalizer H) (hD : S ≤ normalizer D) (hDH : D ≤ H)
    [(D.subgroupOf H).Normal] : S →* MulAut (H ⧸ D.subgroupOf H) where
  toFun g := QuotientGroup.congr _ _ (Offenders.conjugation S H hH g)
    (conjugation_denominator S H D hH hD hDH g)
  map_one' := by
    apply MulEquiv.ext
    intro w
    induction w using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk' _ (Offenders.conjugation S H hH 1 x) = QuotientGroup.mk' _ x
      rw [map_one]
      rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro w
    induction w using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk' _ (Offenders.conjugation S H hH (g*h) x) =
        QuotientGroup.mk' _ (Offenders.conjugation S H hH g (Offenders.conjugation S H hH h x))
      rw [map_mul]
      rfl

private theorem quotientConjugation_apply (S H D : Subgroup G)
    (hH : S ≤ normalizer H) (hD : S ≤ normalizer D) (hDH : D ≤ H)
    [(D.subgroupOf H).Normal] (g : S) (x : H) :
    quotientConjugation S H D hH hD hDH g (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (Offenders.conjugation S H hH g x) := rfl

private theorem quotientConjugation_kills (S H D Q : Subgroup G)
    (hH : S ≤ normalizer H) (hD : S ≤ normalizer D) (hDH : D ≤ H)
    [(D.subgroupOf H).Normal] (hc : ⁅H,Q⁆ ≤ D) :
    Q.subgroupOf S ≤ (quotientConjugation S H D hH hD hDH).ker := by
  intro g hg
  apply MulEquiv.ext
  intro w
  induction w using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk' _ (Offenders.conjugation S H hH g x) = QuotientGroup.mk' _ x
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (g : G) * (x : G) * (g : G)⁻¹ / (x : G) ∈ D
    have hh := hc (show ⁅(g : G),(x : G)⁆ ∈ ⁅H,Q⁆ by
      rw [commutator_comm]; exact commutator_mem_commutator hg x.property)
    simpa only [commutatorElement_def, div_eq_mul_inv] using hh

variable {M : Type*} [Group M] {R : Subgroup M}

/-- An action on the literal neighboring quotient, with its actual local projection. -/
structure Action (a b d : Vertex R) where
  normal : ((fixedCore R a).subgroupOf (carrier a b d)).Normal
  elementary : letI := normal
    IsElementaryAbelian 2 (carrier a b d ⧸ (fixedCore R a).subgroupOf (carrier a b d))
  projection : stabilizer R a →* SL
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker = (Q R a).subgroupOf (stabilizer R a)
  action : letI := normal
    SL →* MulAut (carrier a b d ⧸ (fixedCore R a).subgroupOf (carrier a b d))
  conjugation : letI := normal
    ∀ (g : stabilizer R a) (x y : carrier a b d),
      (y : FreeAmalgam R) = (g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
      action (projection g) (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ y

namespace Action
variable {a b d : Vertex R} (A : Action a b d)

/-- Binary linearization of this exact quotient action. -/
noncomputable def representation :
    letI := A.normal
    letI := A.elementary
    Representation (ZMod 2) SL
      (Additive (carrier a b d ⧸ (fixedCore R a).subgroupOf (carrier a b d))) := by
  let := A.normal
  let := A.elementary
  exact Offenders.linearize A.action

/-- The image of the actual Z-layer in the extension quotient. -/
noncomputable def natural :
    letI := A.normal
    letI := A.elementary
    Subrepresentation A.representation := by
  let := A.normal
  let := A.elementary
  let q := QuotientGroup.mk' ((fixedCore R a).subgroupOf (carrier a b d))
  let N := ((Z R a).subgroupOf (carrier a b d)).map q
  refine { toSubmodule := AddSubgroup.toZModSubmodule 2 N.toAddSubgroup
           apply_mem_toSubmodule := ?_ }
  intro g w hw
  change w.toMul ∈ N at hw
  obtain ⟨z,hz,hzw⟩ := hw
  obtain ⟨g₀,rfl⟩ := A.projection_surjective g
  have hZ : Z R a ≤ carrier a b d :=
    (show Z R a ≤ layer a b d from le_sup_right).trans le_sup_left
  have hy : (g₀ : FreeAmalgam R) * (z : FreeAmalgam R) * (g₀ : FreeAmalgam R)⁻¹ ∈ Z R a :=
    le_normalizer_iff.mp (Z_normalized R a) g₀ g₀.property z hz
  let y : carrier a b d := ⟨_,hZ hy⟩
  have he := A.conjugation g₀ z y rfl
  change A.action (A.projection g₀) w.toMul ∈ N
  rw [← hzw, he]
  exact mem_map_of_mem q hy

/-- The precise natural-module identification needed by the checked cocycle theorem.
This property is not assumed by `action_nonempty`; constructing it is a further proof. -/
def HasNaturalMarking : Prop :=
  letI := A.normal
  letI := A.elementary
  ∃ (marking : SL ≃* SL)
    (e : A.natural.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
    ∀ g v, e (A.natural.toRepresentation g v) =
      Representation.specialLinearNatural (k := ZMod 2) 3 (marking g) (e v)

end Action

variable [Finite M] {L : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R} (common : CommonFacts R source geometry)

include common in
/-- The source data construct an action of the genuine local SL3(2) quotient. -/
theorem action_nonempty (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) : Nonempty (Action a b d) := by
  let S := stabilizer R a
  let H := carrier a b d
  let D := fixedCore R a
  let hn := denominator_normal common a b d ha hB
  let hH := carrier_normalized common a b d ha hab hB
  let hD := DistanceEight.PathCentrality.fixedCore_normalized R a
  let F := quotientConjugation S H D hH hD le_sup_right
  obtain ⟨π,hπ,hker⟩ := SpanOffender.span_local_projection (source := source) a ha
  have hkill : π.ker ≤ F.ker := by
    rw [hker]
    exact quotientConjugation_kills S H D (Q R a) hH hD le_sup_right
      (carrier_kernel_commutator_le_fixedCore common a b d ha hab hdb hB)
  let ρ := π.liftOfSurjective hπ ⟨F,hkill⟩
  have hρ (g : S) : ρ (π g) = F g := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨{
    normal := hn
    elementary := quotient_elementary common a b d ha hab hdb hB
    projection := π
    projection_surjective := hπ
    projection_kernel := hker
    action := ρ
    conjugation := ?_ }⟩
  intro g x y hy
  rw [hρ]
  change QuotientGroup.mk' _ (Offenders.conjugation S H hH g x) = QuotientGroup.mk' _ y
  congr 1
  exact Subtype.ext hy.symm

include common in
/-- A nonidentity involution in the actual neighboring kernel image fixes every
neighboring displacement vector. No order-two lift is asserted. -/
theorem fixed_involution_exists (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) (hne : Q R a ≠ Q R d)
    (A : Action a b d) :
    letI := A.normal
    letI := A.elementary
    ∃ g : SL, g ^ 2 = 1 ∧ g ≠ 1 ∧
      ∀ x : carrier a b d, (x : FreeAmalgam R) ∈ ⁅Z R d,Q R b⁆ →
        A.representation g (Additive.ofMul (QuotientGroup.mk' _ x)) =
          Additive.ofMul (QuotientGroup.mk' _ x) := by
  let := A.normal
  let := A.elementary
  let S := stabilizer R a
  let J := (Q R d).subgroupOf S
  let T := J.map A.projection
  have hJS : Q R d ≤ S := neighbor_kernel_le_stabilizer a b d ha hab hdb
  have hJ : IsPGroup 2 J :=
    (Q_isPGroup R source.two_group source.core_le d (neighbor_color a b d ha hab hdb)).of_equiv
      (subgroupOfEquivOfLe hJS).symm
  have hT : IsPGroup 2 T := hJ.map A.projection
  have hneT : T ≠ ⊥ := by
    intro ht
    have hjker : J ≤ A.projection.ker := (Subgroup.map_eq_bot_iff _).mp ht
    rw [A.projection_kernel] at hjker
    have hda : Q R d ≤ Q R a := fun x hx => hjker (show (⟨x,hJS hx⟩ : S) ∈ J from hx)
    apply neighbor_kernel_not_centralizes common a b d ha hab hdb hne
    exact hda.trans ((le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))).trans
      (centralizer_le (U_le_Z a)))
  have hdiv : 2 ∣ Nat.card T := by
    rcases hT.card_eq_or_dvd with hone | hdiv
    · exact (hneT (eq_bot_of_card_le T hone.le)).elim
    · exact hdiv
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 hdiv
  have hg' := (orderOf_eq_prime_iff (p := 2)).mp hg
  refine ⟨g, congrArg Subtype.val hg'.1, ?_, ?_⟩
  · intro he
    exact hg'.2 (Subtype.ext he)
  · intro x hx
    obtain ⟨j,hj,hjg⟩ := g.property
    have hfix := neighbor_displacement_centralizes common a b d ha hab hdb hx j hj
    have he : (x : FreeAmalgam R) =
        (j : FreeAmalgam R) * (x : FreeAmalgam R) * (j : FreeAmalgam R)⁻¹ := by
      rw [hfix, mul_inv_cancel_right]
    have hh := A.conjugation j x x he
    change Additive.ofMul (A.action (g : SL) (QuotientGroup.mk' _ x)) = _
    rw [← hjg, hh]

omit [Finite M] in
/-- Membership in the concrete natural image has the literal product preimage. -/
theorem Action.mem_natural_iff {a b d : Vertex R} (A : Action a b d)
    (x : carrier a b d) :
    letI := A.normal
    letI := A.elementary
    Additive.ofMul (QuotientGroup.mk' ((fixedCore R a).subgroupOf (carrier a b d)) x) ∈
      A.natural.toSubmodule ↔ (x : FreeAmalgam R) ∈ Z R a ⊔ fixedCore R a := by
  let := A.normal
  let := A.elementary
  let q := QuotientGroup.mk' ((fixedCore R a).subgroupOf (carrier a b d))
  change x ∈ (((Z R a).subgroupOf (carrier a b d)).map q).comap q ↔ _
  rw [comap_map_eq, QuotientGroup.ker_mk']
  rw [← subgroupOf_sup
    (show Z R a ≤ carrier a b d from
      (show Z R a ≤ layer a b d from le_sup_right).trans le_sup_left)
    (show fixedCore R a ≤ carrier a b d from le_sup_right)]
  rfl

include common in
/-- The fixed central summand of Z disappears on adjoining D_alpha. -/
theorem Z_sup_fixedCore_eq (a : Vertex R) (ha : color R a = false) :
    Z R a ⊔ fixedCore R a = U R a ⊔ fixedCore R a := by
  let data : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z,common.natural,common.decomposition,common.disjoint⟩
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [data.decomposition_at a ha]
    refine sup_le le_sup_left (le_trans ?_ le_sup_right)
    exact le_inf (inf_le_left.trans (by
      rw [← common.X_eq_Z a ha]; exact omegaCenter_le _))
      (inf_le_right.trans (centralizer_le (Ltilde_le_stabilizer a)))
  · exact sup_le_sup_right (U_le_Z a) _

include common in
/-- Natural-image membership is exactly the requested U_alpha D_alpha bound. -/
theorem natural_preimage (a b d : Vertex R) (ha : color R a = false)
    (A : Action a b d) (x : carrier a b d) :
    letI := A.normal
    letI := A.elementary
    Additive.ofMul (QuotientGroup.mk' ((fixedCore R a).subgroupOf (carrier a b d)) x) ∈
      A.natural.toSubmodule ↔ (x : FreeAmalgam R) ∈ U R a ⊔ fixedCore R a := by
  rw [A.mem_natural_iff, Z_sup_fixedCore_eq common a ha]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound.Extension
