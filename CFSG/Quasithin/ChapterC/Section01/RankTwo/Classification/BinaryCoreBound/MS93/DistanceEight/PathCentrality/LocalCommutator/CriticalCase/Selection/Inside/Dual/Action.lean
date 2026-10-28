module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Dual.Groups
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Cocycle
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions

/-!
# Conjugation on the point extension

Conjugation on <x>Z_cD_c/D_c descends through the actual local projection
G_c -> SL3(2), since Q_c acts trivially. Its distinguished subrepresentation
is the literal image of Z_c. For unequal Q_a and Q_c, equal kernel orders
show that Q_a has a nontrivial two-group image. An involution in that image
fixes x, because x belongs to Z_a and [Z_a,Q_a] = 1.

The quotient-action and natural-image constructions adapt
Reduction/Escape/EdgeTransfer/Extension/Action. The actor providing the
involution here is precisely Q_a, with the original point x.
Source: MS93 (1993), (4.4.1), claim (2), printed p.891; (1.5)(i), p.843.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Dual
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

/-- An action on the literal point quotient, with its actual local projection. -/
structure Action (c : Vertex R) (point : FreeAmalgam R) where
  normal : ((fixedCore R c).subgroupOf (carrier c point)).Normal
  elementary : letI := normal
    IsElementaryAbelian 2 (carrier c point ⧸ (fixedCore R c).subgroupOf (carrier c point))
  projection : stabilizer R c →* SL
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker = (Q R c).subgroupOf (stabilizer R c)
  action : letI := normal
    SL →* MulAut (carrier c point ⧸ (fixedCore R c).subgroupOf (carrier c point))
  conjugation : letI := normal
    ∀ (g : stabilizer R c) (x y : carrier c point),
      (y : FreeAmalgam R) = (g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
      action (projection g) (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ y

namespace Action
variable {c : Vertex R} {point : FreeAmalgam R} (A : Action c point)

/-- Binary linearization of this exact quotient action. -/
noncomputable def representation :
    letI := A.normal
    letI := A.elementary
    Representation (ZMod 2) SL
      (Additive (carrier c point ⧸ (fixedCore R c).subgroupOf (carrier c point))) := by
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
  let q := QuotientGroup.mk' ((fixedCore R c).subgroupOf (carrier c point))
  let N := ((Z R c).subgroupOf (carrier c point)).map q
  refine { toSubmodule := AddSubgroup.toZModSubmodule 2 N.toAddSubgroup
           apply_mem_toSubmodule := ?_ }
  intro g w hw
  change w.toMul ∈ N at hw
  obtain ⟨z,hz,hzw⟩ := hw
  obtain ⟨g₀,rfl⟩ := A.projection_surjective g
  have hZ : Z R c ≤ carrier c point :=
    (show Z R c ≤ layer c point from le_sup_right).trans le_sup_left
  have hy : (g₀ : FreeAmalgam R) * (z : FreeAmalgam R) * (g₀ : FreeAmalgam R)⁻¹ ∈ Z R c :=
    le_normalizer_iff.mp (Z_normalized R c) g₀ g₀.property z hz
  let y : carrier c point := ⟨_,hZ hy⟩
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
  {geometry : Geometry R}

include source in
private theorem local_projection (c : Vertex R) (ha : color R c = false) :
    ∃ π : stabilizer R c →* SL, Function.Surjective π ∧
      π.ker = (Q R c).subgroupOf (stabilizer R c) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl, ← map_map,
      ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  refine ⟨source.projection.comp e.symm.toMonoidHom,
    source.projection_surjective.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, source.projection_kernel, ← hQ]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    change e.symm (e y) ∈ pCore 2 M
    rw [MulEquiv.symm_apply_apply]
    exact hy

/-- Construct the genuine SL3(2) action on the literal point quotient. -/
theorem action_nonempty (modules : ModuleFacts source geometry)
    {c : Vertex R} {point : FreeAmalgam R} (hc : color R c = false)
    (data : PointData c point) : Nonempty (Action c point) := by
  let S := stabilizer R c
  let H := carrier c point
  let D := fixedCore R c
  let hn := denominator_normal modules hc data
  let hH := carrier_normalized modules hc data
  let hD := PathCentrality.fixedCore_normalized R c
  let F := quotientConjugation S H D hH hD le_sup_right
  obtain ⟨π,hπ,hker⟩ := local_projection (source := source) c hc
  have hkill : π.ker ≤ F.ker := by
    rw [hker]
    exact quotientConjugation_kills S H D (Q R c) hH hD le_sup_right
      (carrier_kernel_commutator_le_fixedCore modules hc data)
  let ρ := π.liftOfSurjective hπ ⟨F,hkill⟩
  have hρ (g : S) : ρ (π g) = F g := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨{
    normal := hn
    elementary := quotient_elementary modules hc data
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

/-- The image of the actual Q_a contains an involution fixing the point.
Only its image must have order two; no involution lift is assumed. -/
theorem fixed_involution_exists (common : CommonFacts R source geometry)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hne : Q R c ≠ Q R a)
    (point : FreeAmalgam R) (hp : point ∈ ⁅Z R a,Q R c⁆)
    (A : Action c point) :
    letI := A.normal
    letI := A.elementary
    ∃ g : SL, g ^ 2 = 1 ∧ g ≠ 1 ∧
      ∀ x : carrier c point, (x : FreeAmalgam R) = point →
        A.representation g (Additive.ofMul (QuotientGroup.mk' _ x)) =
          Additive.ofMul (QuotientGroup.mk' _ x) := by
  let := A.normal
  let := A.elementary
  let S := stabilizer R c
  let J := (Q R a).subgroupOf S
  let T := J.map A.projection
  have hJS : Q R a ≤ S := Q_le_stabilizer_of_dist_two R a c ha hd
  have hJ : IsPGroup 2 J :=
    (Q_isPGroup R source.two_group source.core_le a ha).of_equiv
      (subgroupOfEquivOfLe hJS).symm
  have hT : IsPGroup 2 T := hJ.map A.projection
  have hneT : T ≠ ⊥ := by
    intro ht
    have hjker : J ≤ A.projection.ker := (Subgroup.map_eq_bot_iff _).mp ht
    rw [A.projection_kernel] at hjker
    have hac : Q R a ≤ Q R c := fun x hx => hjker (show (⟨x,hJS hx⟩ : S) ∈ J from hx)
    let : Finite S := finite_stabilizer R c
    let : Finite (Q R c) := Finite.of_injective
      (inclusion (show Q R c ≤ S from fun _ hx => hx.1)) (inclusion_injective _)
    exact hne (eq_of_le_of_card_ge hac
      (by rw [source.Q_card c hc, source.Q_card a ha])).symm
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
    have hpointZ := (displacement_le_U common ha hd).trans (U_le_Z R a) hp
    have hfix := (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes a ha)) hpointZ j hj
    have he : (x : FreeAmalgam R) =
        (j : FreeAmalgam R) * (x : FreeAmalgam R) * (j : FreeAmalgam R)⁻¹ := by
      rw [hx, hfix, mul_inv_cancel_right]
    have hh := A.conjugation j x x he
    change Additive.ofMul (A.action (g : SL) (QuotientGroup.mk' _ x)) = _
    rw [← hjg, hh]

omit [Finite M] in
/-- Membership in the concrete natural image has the literal product preimage. -/
theorem Action.mem_natural_iff {c : Vertex R} {point : FreeAmalgam R} (A : Action c point)
    (x : carrier c point) :
    letI := A.normal
    letI := A.elementary
    Additive.ofMul (QuotientGroup.mk' ((fixedCore R c).subgroupOf (carrier c point)) x) ∈
      A.natural.toSubmodule ↔ (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c := by
  let := A.normal
  let := A.elementary
  let q := QuotientGroup.mk' ((fixedCore R c).subgroupOf (carrier c point))
  change x ∈ (((Z R c).subgroupOf (carrier c point)).map q).comap q ↔ _
  rw [comap_map_eq, QuotientGroup.ker_mk']
  rw [← subgroupOf_sup
    (show Z R c ≤ carrier c point from
      (show Z R c ≤ layer c point from le_sup_right).trans le_sup_left)
    (show fixedCore R c ≤ carrier c point from le_sup_right)]
  rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Dual
