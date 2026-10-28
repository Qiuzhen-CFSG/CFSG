module

public import Theory.GroupTheory.NoncentralChiefRefinement.Accounting
public import Theory.Representation.SubspaceQuotient

/-!
# Chief refinements from a two-factor binary flag

Let `P` be an invariant subspace of a binary representation. An equivariant
surjection from a normal subgroup pulls back `0 < P < M` to ambient-normal
nodes. Restricting the surjection to the middle node, and composing it with
the actual module quotient, gives the two relative quotient coordinates.
Irreducibility makes these intervals chief; nontrivial action makes them
noncentral. This argument does not require a two-perfect actor.

For a surjection from a literal section, refine below its kernel. For an
embedding in a literal section, take the preimage of its image and use the
inverse image coordinates, whose kernel is exactly the original denominator;
then refine above the image. Concatenation and equivariant Jordan–Hölder give
the lower bound two for every chief series with the original endpoints.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
14.7.70, printed p.1074/PDF p.1091: the two natural and two dual-natural
noncentral chief factors. The source-specific maps and flag hypotheses are
supplied by the chapter consumer. No chiefness or factor count is an input.
-/

@[expose] public section

open Subgroup
namespace NoncentralChiefRefinement.BinaryFlag
variable {K M : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
variable {A B : NormalNode K} {ρ : Representation (ZMod 2) K M}

/-- A homomorphism from an ambient-normal subgroup with its literal conjugation action. -/
structure Map (B : NormalNode K) (ρ : Representation (ZMod 2) K M) where
  hom : B.val →* Multiplicative M
  equivariant (k : K) (b : B.val) :
    (hom (MulAut.conjNormal k b)).toAdd = ρ k (hom b).toAdd

namespace Map
variable (q : Map B ρ)

/-- The ambient-normal pullback of an invariant binary subspace. -/
def preimage (P : Subrepresentation ρ) : NormalNode K :=
  ⟨{ carrier := {x | ∃ hx : x ∈ B.val, (q.hom ⟨x, hx⟩).toAdd ∈ P}
     one_mem' := ⟨B.val.one_mem, by change (q.hom 1).toAdd ∈ P; rw [map_one]; exact P.toSubmodule.zero_mem⟩
     mul_mem' := by
       rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
       refine ⟨B.val.mul_mem hx hy, ?_⟩
       change (q.hom (⟨x, hx⟩ * ⟨y, hy⟩)).toAdd ∈ P
       rw [map_mul]
       exact P.toSubmodule.add_mem hx' hy'
     inv_mem' := by
       rintro x ⟨hx, hx'⟩
       refine ⟨B.val.inv_mem hx, ?_⟩
       change (q.hom (⟨x, hx⟩⁻¹)).toAdd ∈ P
       rw [map_inv]
       exact P.toSubmodule.neg_mem hx' },
    ⟨by
      rintro x ⟨hx, hx'⟩ k
      refine ⟨B.property.conj_mem x hx k, ?_⟩
      change (q.hom (MulAut.conjNormal k ⟨x, hx⟩)).toAdd ∈ P
      rw [q.equivariant]
      exact P.apply_mem_toSubmodule k hx'⟩⟩

/-- Every pulled-back node lies in the original upper node. -/
theorem preimage_le (P : Subrepresentation ρ) : q.preimage P ≤ B := fun _ hx => hx.1

/-- Pullback preserves the invariant-subspace flag. -/
theorem preimage_mono {P Q : Subrepresentation ρ} (h : P ≤ Q) :
    q.preimage P ≤ q.preimage Q := fun _ hx => ⟨hx.1, h hx.2⟩

/-- Restriction to the pulled-back subspace, with the original restricted action. -/
def onSubmodule (P : Subrepresentation ρ) : Map (q.preimage P) P.toRepresentation where
  hom :=
    { toFun := fun x => Multiplicative.ofAdd
        ⟨(q.hom ⟨x.val, (q.preimage_le P) x.property⟩).toAdd, x.property.2⟩
      map_one' := by apply Multiplicative.toAdd.injective; apply Subtype.ext; exact congrArg Multiplicative.toAdd q.hom.map_one
      map_mul' x y := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd
          (q.hom.map_mul ⟨x.val, (q.preimage_le P) x.property⟩
            ⟨y.val, (q.preimage_le P) y.property⟩) }
  equivariant k x := by
    apply Subtype.ext
    exact q.equivariant k ⟨x.val, (q.preimage_le P) x.property⟩

/-- Surjectivity restricts to the actual preimage of the subspace. -/
theorem onSubmodule_surjective (P : Subrepresentation ρ)
    (hs : Function.Surjective q.hom) : Function.Surjective (q.onSubmodule P).hom := by
  intro v
  obtain ⟨b, hb⟩ := hs (Multiplicative.ofAdd v.toAdd.val)
  have hm : b.val ∈ (q.preimage P).val := ⟨b.property, by rw [hb]; exact v.toAdd.property⟩
  refine ⟨⟨b.val, hm⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hb

/-- The original homomorphism followed by the literal vector-space quotient. -/
def onQuotient (P : Subrepresentation ρ) : Map B P.quotientRepresentation where
  hom := P.toSubmodule.mkQ.toAddMonoidHom.toMultiplicative.comp q.hom
  equivariant k b := by
    change P.toSubmodule.mkQ (q.hom (MulAut.conjNormal k b)).toAdd = _
    rw [q.equivariant]
    rfl

/-- The map to the module quotient remains surjective. -/
theorem onQuotient_surjective (P : Subrepresentation ρ)
    (hs : Function.Surjective q.hom) : Function.Surjective (q.onQuotient P).hom := by
  intro v
  obtain ⟨m, hm⟩ := P.toSubmodule.mkQ_surjective v.toAdd
  obtain ⟨b, hb⟩ := hs (Multiplicative.ofAdd m)
  refine ⟨b, ?_⟩
  apply Multiplicative.toAdd.injective
  change P.toSubmodule.mkQ (q.hom b).toAdd = v.toAdd
  rw [hb]
  exact hm

/-- Write one module as a single coordinate, for the homogeneous-section API. -/
def oneCopy : Multiplicative M ≃* Multiplicative (Fin 1 → M) where
  toFun v := Multiplicative.ofAdd (fun _ => v.toAdd)
  invFun v := Multiplicative.ofAdd (v.toAdd 0)
  left_inv _ := rfl
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg v.toAdd (Subsingleton.elim _ _)
  map_mul' _ _ := rfl

/-- The first isomorphism theorem, retaining the specified ambient action. -/
noncomputable def coordinates (hs : Function.Surjective q.hom)
    (hk : q.hom.ker = A.val.subgroupOf B.val) : SectionCoordinates A B ρ 1 where
  equiv := ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q.hom hs)).trans oneCopy
  equivariant k x i := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
    exact q.equivariant k b

/-- The relative quotient coordinate agrees with the given homomorphism on representatives. -/
theorem coordinates_mk (hs : Function.Surjective q.hom)
    (hk : q.hom.ker = A.val.subgroupOf B.val) (b : B.val) (i : Fin 1) :
    ((q.coordinates hs hk).equiv (QuotientGroup.mk' (A.val.subgroupOf B.val) b)).toAdd i =
      (q.hom b).toAdd := rfl

/-- The lower flag kernel is precisely the pulled-back zero subspace. -/
theorem onSubmodule_kernel (P : Subrepresentation ρ) :
    (q.onSubmodule P).hom.ker = (q.preimage ⊥).val.subgroupOf (q.preimage P).val := by
  ext x
  change (q.onSubmodule P).hom x = 1 ↔ _
  constructor
  · intro hx
    refine ⟨(q.preimage_le P) x.property, ?_⟩
    exact congrArg (fun v : Multiplicative P.toSubmodule => v.toAdd.val) hx
  · intro hx
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hx.2

/-- The upper flag kernel is precisely the pulled-back invariant subspace. -/
theorem onQuotient_kernel (P : Subrepresentation ρ) :
    (q.onQuotient P).hom.ker = (q.preimage P).val.subgroupOf B.val := by
  ext b
  change P.toSubmodule.mkQ (q.hom b).toAdd = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun h => ⟨b.property, h⟩, fun h => h.2⟩

/-- Equivariant one-copy coordinates for the lower literal flag quotient. -/
noncomputable def submoduleCoordinates (P : Subrepresentation ρ)
    (hs : Function.Surjective q.hom) :
    SectionCoordinates (q.preimage ⊥) (q.preimage P) P.toRepresentation 1 :=
  (q.onSubmodule P).coordinates (q.onSubmodule_surjective P hs) (q.onSubmodule_kernel P)

/-- Equivariant one-copy coordinates for the upper literal flag quotient. -/
noncomputable def quotientCoordinates (P : Subrepresentation ρ)
    (hs : Function.Surjective q.hom) :
    SectionCoordinates (q.preimage P) B P.quotientRepresentation 1 :=
  (q.onQuotient P).coordinates (q.onQuotient_surjective P hs) (q.onQuotient_kernel P)

/-- The lower coordinates are the original map, restricted to its subspace preimage. -/
theorem submoduleCoordinates_mk (P : Subrepresentation ρ)
    (hs : Function.Surjective q.hom) (b : (q.preimage P).val) (i : Fin 1) :
    (((q.submoduleCoordinates P hs).equiv (QuotientGroup.mk'
      ((q.preimage ⊥).val.subgroupOf (q.preimage P).val) b)).toAdd i).val =
        (q.hom ⟨b.val, (q.preimage_le P) b.property⟩).toAdd := rfl

/-- The upper coordinates use exactly the original map and the module quotient map. -/
theorem quotientCoordinates_mk (P : Subrepresentation ρ)
    (hs : Function.Surjective q.hom) (b : B.val) (i : Fin 1) :
    ((q.quotientCoordinates P hs).equiv
      (QuotientGroup.mk' ((q.preimage P).val.subgroupOf B.val) b)).toAdd i =
        P.toSubmodule.mkQ (q.hom b).toAdd := rfl

/-- Both pulled-back intervals are chief and noncentral two-factors. -/
theorem flag_chief (P : Subrepresentation ρ) (hs : Function.Surjective q.hom)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v) :
    q.preimage ⊥ ⋖ q.preimage P ∧ q.preimage P ⋖ B ∧
      IsNoncentralTwo (q.preimage ⊥) (q.preimage P) ∧ IsNoncentralTwo (q.preimage P) B :=
  ⟨(q.submoduleCoordinates P hs).covBy (q.preimage_mono bot_le) hP,
    (q.quotientCoordinates P hs).covBy (q.preimage_le P) hQ,
    ⟨(q.submoduleCoordinates P hs).isPGroup,
      (q.submoduleCoordinates P hs).not_isCentral (by decide) hP⟩,
    ⟨(q.quotientCoordinates P hs).isPGroup,
      (q.quotientCoordinates P hs).not_isCentral (by decide) hQ⟩⟩

/-- The two adjacent flag intervals form a chief series of length and count two. -/
theorem exists_chief_pair (P : Subrepresentation ρ) (hs : Function.Surjective q.hom)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v) :
    ∃ s : ChiefSeries K, s.head = q.preimage ⊥ ∧ s.last = B ∧
      s.length = 2 ∧ s.noncentralTwoCount = 2 := by
  let c := q.submoduleCoordinates P hs
  let d := q.quotientCoordinates P hs
  let s := c.chiefSeries hP
  let t := d.chiefSeries hQ
  have hst : s.last = t.head := (c.chiefSeries_last hP).trans
    (d.chiefSeries_head hQ (q.preimage_le P)).symm
  refine ⟨s.smash t hst, ?_, ?_, rfl, ?_⟩
  · exact (RelSeries.head_smash hst).trans
      (c.chiefSeries_head hP (q.preimage_mono bot_le))
  · exact (RelSeries.last_smash hst).trans (d.chiefSeries_last hQ)
  · rw [ChiefSeries.noncentralTwoCount_smash]
    exact congrArg₂ (· + ·) (c.chiefSeries_count hP) (d.chiefSeries_count hQ)

end Map

/-- Refine the intervals below and above a given chief series; concatenation cannot decrease its count. -/
theorem extend_count [Finite K] {C D : NormalNode K}
    (hAC : A ≤ C) (hDB : D ≤ B) (s : ChiefSeries K)
    (hs0 : s.head = C) (hsl : s.last = D) :
    ∃ t : ChiefSeries K, t.head = A ∧ t.last = B ∧
      s.noncentralTwoCount ≤ t.noncentralTwoCount := by
  obtain ⟨u, hu0, hul⟩ := exists_chiefSeries A C hAC
  obtain ⟨v, hv0, hvl⟩ := exists_chiefSeries D B hDB
  have hus : u.last = s.head := hul.trans hs0.symm
  have husv : (u.smash s hus).last = v.head :=
    (RelSeries.last_smash hus).trans (hsl.trans hv0.symm)
  refine ⟨(u.smash s hus).smash v husv, ?_, ?_, ?_⟩
  · simpa only [RelSeries.head_smash] using hu0
  · exact (RelSeries.last_smash husv).trans hvl
  · rw [ChiefSeries.noncentralTwoCount_smash, ChiefSeries.noncentralTwoCount_smash]
    omega

/-- Compose a map on the literal relative quotient with its actual quotient projection. -/
def ofSection (f : Section A B →* Multiplicative M)
    (he : ∀ k x, (f (sectionAction A B k x)).toAdd = ρ k (f x).toAdd) : Map B ρ where
  hom := f.comp (QuotientGroup.mk' (A.val.subgroupOf B.val))
  equivariant k b := he k (QuotientGroup.mk' (A.val.subgroupOf B.val) b)

/-- A surjection from the section is also a surjection from its upper subgroup. -/
theorem ofSection_surjective (f : Section A B →* Multiplicative M)
    (he : ∀ k x, (f (sectionAction A B k x)).toAdd = ρ k (f x).toAdd)
    (hf : Function.Surjective f) : Function.Surjective (ofSection f he).hom :=
  hf.comp (QuotientGroup.mk'_surjective _)

/-- The original lower node lies in the kernel of the pulled-back section map. -/
theorem le_ofSection_kernel (hAB : A ≤ B) (f : Section A B →* Multiplicative M)
    (he : ∀ k x, (f (sectionAction A B k x)).toAdd = ρ k (f x).toAdd) :
    A ≤ (ofSection f he).preimage ⊥ := by
  intro x hx
  refine ⟨hAB hx, ?_⟩
  change (f (QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hAB hx⟩)).toAdd = 0
  have hq : QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hAB hx⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hx
  rw [hq, map_one]
  rfl

/-- Two noncentral irreducible binary flag factors in an equivariant quotient give at least two noncentral two-chief factors between the original nodes. -/
theorem exists_refinement_of_surjection [Finite K] (hAB : A ≤ B)
    (P : Subrepresentation ρ)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v)
    (f : Section A B →* Multiplicative M) (hf : Function.Surjective f)
    (he : ∀ k x, (f (sectionAction A B k x)).toAdd = ρ k (f x).toAdd) :
    ∃ s : ChiefSeries K, s.head = A ∧ s.last = B ∧ 2 ≤ s.noncentralTwoCount := by
  obtain ⟨s, hs0, hsl, _, hcount⟩ :=
    (ofSection f he).exists_chief_pair P (ofSection_surjective f he hf) hP hQ
  obtain ⟨t, ht0, htl, ht⟩ := extend_count (le_ofSection_kernel hAB f he) le_rfl s hs0 hsl
  exact ⟨t, ht0, htl, hcount ▸ ht⟩

/-- The preimage in the original upper subgroup of an equivariant embedded module.
Normality is in the whole actor group. -/
def imageNode (j : Multiplicative M →* Section A B)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) : NormalNode K :=
  ⟨{ carrier := {x | ∃ hx : x ∈ B.val,
        QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hx⟩ ∈ j.range}
     one_mem' := ⟨B.val.one_mem, j.range.one_mem⟩
     mul_mem' := by
       rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
       refine ⟨B.val.mul_mem hx hy, ?_⟩
       exact j.range.mul_mem hx' hy'
     inv_mem' := by
       rintro x ⟨hx, hx'⟩
       exact ⟨B.val.inv_mem hx, j.range.inv_mem hx'⟩ },
    ⟨by
      rintro x ⟨hx, v, hv⟩ k
      refine ⟨B.property.conj_mem x hx k, Multiplicative.ofAdd (ρ k v.toAdd), ?_⟩
      rw [he]
      change sectionAction A B k (j v) = _
      rw [hv]
      rfl⟩⟩

/-- The preimage of the embedded module lies in the original upper node. -/
theorem imageNode_le (j : Multiplicative M →* Section A B)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) : imageNode j he ≤ B :=
  fun _ hx => hx.1

/-- The original denominator is contained in the preimage of the embedded module. -/
theorem le_imageNode (hAB : A ≤ B) (j : Multiplicative M →* Section A B)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) : A ≤ imageNode j he := by
  intro x hx
  refine ⟨hAB hx, ?_⟩
  have hq : QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hAB hx⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hx
  rw [hq]
  exact j.range.one_mem

/-- The literal quotient projection, restricted to the preimage of the module image. -/
def imageProjection (j : Multiplicative M →* Section A B)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) :
    (imageNode j he).val →* j.range where
  toFun x := ⟨QuotientGroup.mk' (A.val.subgroupOf B.val)
    ⟨x.val, (imageNode_le j he) x.property⟩, x.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Coordinates on the image preimage, using the inverse of the actual embedding. -/
noncomputable def ofEmbedding (j : Multiplicative M →* Section A B)
    (hj : Function.Injective j)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) : Map (imageNode j he) ρ where
  hom := (MonoidHom.ofInjective hj).symm.toMonoidHom.comp (imageProjection j he)
  equivariant k b := by
    apply Multiplicative.ofAdd.injective
    apply hj
    change j ((MonoidHom.ofInjective hj).symm (imageProjection j he
      (MulAut.conjNormal k b))) = j (Multiplicative.ofAdd (ρ k _))
    rw [MonoidHom.apply_ofInjective_symm, he]
    change _ = sectionAction A B k
      (j ((MonoidHom.ofInjective hj).symm (imageProjection j he b)))
    rw [MonoidHom.apply_ofInjective_symm]
    rfl

/-- Composing the image coordinates with the embedding recovers the literal quotient projection. -/
theorem ofEmbedding_apply (j : Multiplicative M →* Section A B)
    (hj : Function.Injective j)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v)))
    (b : (imageNode j he).val) :
    j ((ofEmbedding j hj he).hom b) = QuotientGroup.mk' (A.val.subgroupOf B.val)
      ⟨b.val, (imageNode_le j he) b.property⟩ :=
  MonoidHom.apply_ofInjective_symm hj _

/-- The image preimage maps onto the embedded module. -/
theorem ofEmbedding_surjective (j : Multiplicative M →* Section A B)
    (hj : Function.Injective j)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) :
    Function.Surjective (ofEmbedding j hj he).hom := by
  intro v
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) (j v)
  have hm : b.val ∈ (imageNode j he).val := ⟨b.property, v, hb.symm⟩
  refine ⟨⟨b.val, hm⟩, hj ?_⟩
  rw [ofEmbedding_apply]
  exact hb

/-- The kernel of the image coordinates is exactly the original denominator. -/
theorem ofEmbedding_kernel (hAB : A ≤ B) (j : Multiplicative M →* Section A B)
    (hj : Function.Injective j)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) :
    (ofEmbedding j hj he).preimage ⊥ = A := by
  apply le_antisymm
  · rintro x ⟨hx, hx'⟩
    have hzero : (ofEmbedding j hj he).hom ⟨x, hx⟩ = 1 := hx'
    have h := ofEmbedding_apply j hj he ⟨x, hx⟩
    rw [hzero, map_one] at h
    exact (QuotientGroup.eq_one_iff
      (N := A.val.subgroupOf B.val) ⟨x, (imageNode_le j he) hx⟩).mp h.symm
  · intro x hx
    have hm := le_imageNode hAB j he hx
    refine ⟨hm, ?_⟩
    have hzero : (ofEmbedding j hj he).hom ⟨x, hm⟩ = 1 := by
      apply hj
      rw [ofEmbedding_apply, map_one]
      exact (QuotientGroup.eq_one_iff _).mpr hx
    exact hzero

/-- Two noncentral irreducible binary flag factors in an equivariantly embedded module give at least two noncentral two-chief factors between the original nodes. -/
theorem exists_refinement_of_embedding [Finite K] (hAB : A ≤ B)
    (P : Subrepresentation ρ)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v)
    (j : Multiplicative M →* Section A B) (hj : Function.Injective j)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v))) :
    ∃ s : ChiefSeries K, s.head = A ∧ s.last = B ∧ 2 ≤ s.noncentralTwoCount := by
  obtain ⟨s, hs0, hsl, _, hcount⟩ :=
    (ofEmbedding j hj he).exists_chief_pair P (ofEmbedding_surjective j hj he) hP hQ
  rw [ofEmbedding_kernel hAB j hj he] at hs0
  obtain ⟨t, ht0, htl, ht⟩ := extend_count le_rfl (imageNode_le j he) s hs0 hsl
  exact ⟨t, ht0, htl, hcount ▸ ht⟩

/-- The surjective flag bound holds for every chief series with the original endpoints. -/
theorem count_ge_two_of_surjection [Finite K] (hAB : A ≤ B)
    (P : Subrepresentation ρ)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v)
    (f : Section A B →* Multiplicative M) (hf : Function.Surjective f)
    (he : ∀ k x, (f (sectionAction A B k x)).toAdd = ρ k (f x).toAdd)
    (s : ChiefSeries K) (hs0 : s.head = A) (hsl : s.last = B) :
    2 ≤ s.noncentralTwoCount := by
  obtain ⟨t, ht0, htl, ht⟩ := exists_refinement_of_surjection hAB P hP hQ f hf he
  rw [s.noncentralTwoCount_eq t (hs0.trans ht0.symm) (hsl.trans htl.symm)]
  exact ht

/-- The embedded flag bound holds for every chief series with the original endpoints. -/
theorem count_ge_two_of_embedding [Finite K] (hAB : A ≤ B)
    (P : Subrepresentation ρ)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v)
    (j : Multiplicative M →* Section A B) (hj : Function.Injective j)
    (he : ∀ k v, j (Multiplicative.ofAdd (ρ k v)) =
      sectionAction A B k (j (Multiplicative.ofAdd v)))
    (s : ChiefSeries K) (hs0 : s.head = A) (hsl : s.last = B) :
    2 ≤ s.noncentralTwoCount := by
  obtain ⟨t, ht0, htl, ht⟩ := exists_refinement_of_embedding hAB P hP hQ j hj he
  rw [s.noncentralTwoCount_eq t (hs0.trans ht0.symm) (hsl.trans htl.symm)]
  exact ht

end NoncentralChiefRefinement.BinaryFlag
