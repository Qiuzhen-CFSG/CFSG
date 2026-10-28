module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.SourceCases

/-!
# Transporting the actual bad-case modules to critical endpoints

A frame is a genuine conjugation carrying the distinguished M-vertex to a
specified vertex. It gives an isomorphism from M onto the entire vertex
stabilizer, whose marked quotient has kernel Q at that vertex. The induced
isomorphism on U transports the source coordinates equivariantly.

The three branch transports retain the invertible maps, common marking,
surjectivity and exact kernel, fixed/moving decompositions, disjointness,
and the outer relative index. In the doubled and central-extension branches,
the fixed part lies in Z, giving X = Z at every source vertex. Thus their
literal source commutator equals the auxiliary X commutator. The outer
branch retains its different X and Z.

These are transport and layer-identification results. They do not prove
the displacement calculation or Source33Bound.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation (3.0), printed p.859, and (3.2)(iii)–(v), printed p.863.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- A genuine conjugation chart from the distinguished local group. -/
structure Frame (R : Subgroup M) (a : Vertex R) where
  element : FreeAmalgam R
  vertex : act R element (alpha R) = a

theorem exists_frame (a : Vertex R) (ha : color R a = false) : Nonempty (Frame R a) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  exact ⟨⟨g, by simp only [alpha, act_mVertex, one_mul]⟩⟩

noncomputable def fixedAt (R : Subgroup M) (a : Vertex R) : Subgroup (FreeAmalgam R) :=
  X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))

namespace Frame
variable {a : Vertex R} (frame : Frame R a)

def conjugation : MulAut (FreeAmalgam R) := MulAut.conj frame.element⁻¹

theorem map_X : (X R (alpha R)).map frame.conjugation.toMonoidHom = X R a := by
  simpa only [conjugation, frame.vertex] using (X_act R frame.element (alpha R)).symm

theorem map_Z : (Z R (alpha R)).map frame.conjugation.toMonoidHom = Z R a := by
  simpa only [conjugation, frame.vertex] using (Z_act R frame.element (alpha R)).symm

theorem map_U : (U R (alpha R)).map frame.conjugation.toMonoidHom = U R a := by
  simpa only [conjugation, frame.vertex] using (U_act R frame.element (alpha R)).symm

theorem map_Q : (Q R (alpha R)).map frame.conjugation.toMonoidHom = Q R a := by
  simpa only [conjugation, frame.vertex] using (Q_act R frame.element (alpha R)).symm

theorem map_Ltilde : (Ltilde R (alpha R)).map frame.conjugation.toMonoidHom = Ltilde R a := by
  simpa only [conjugation, frame.vertex] using (Ltilde_act R frame.element (alpha R)).symm

theorem map_stabilizer : (stabilizer R (alpha R)).map frame.conjugation.toMonoidHom =
    stabilizer R a := by
  simpa only [conjugation, frame.vertex] using (stabilizer_act R frame.element (alpha R)).symm

noncomputable def localEquiv : M ≃* stabilizer R a :=
  (baseEquiv (R := R)).trans ((frame.conjugation.subgroupMap (stabilizer R (alpha R))).trans
    (MulEquiv.subgroupCongr frame.map_stabilizer))

@[simp] theorem localEquiv_val (g : M) :
    (frame.localEquiv g : FreeAmalgam R) = frame.conjugation (embedM R g) := rfl

noncomputable def projection (source : LocalSource L R) : stabilizer R a →* SL :=
  source.projection.comp frame.localEquiv.symm.toMonoidHom

@[simp] theorem projection_localEquiv (source : LocalSource L R) (g : M) :
    frame.projection source (frame.localEquiv g) = source.projection g := by
  simp [projection]

theorem projection_surjective (source : LocalSource L R) :
    Function.Surjective (frame.projection source) :=
  source.projection_surjective.comp frame.localEquiv.symm.surjective

theorem projection_kernel [Finite M] (source : LocalSource L R) :
    (frame.projection source).ker = (Q R a).subgroupOf (stabilizer R a) := by
  ext g
  obtain ⟨m, rfl⟩ := frame.localEquiv.surjective g
  change frame.projection source (frame.localEquiv m) = 1 ↔
    frame.conjugation (embedM R m) ∈ Q R a
  rw [projection_localEquiv, ← frame.map_Q]
  change source.projection m = 1 ↔ frame.conjugation.toMonoidHom (embedM R m) ∈ _
  rw [mem_map_iff_mem frame.conjugation.injective, Q_alpha R source.two_group source.core_le,
    mem_map_iff_mem (embedM_injective R)]
  exact show m ∈ source.projection.ker ↔ m ∈ pCore 2 M from by rw [source.projection_kernel]

noncomputable def movingEquiv : U R (alpha R) ≃* U R a :=
  (frame.conjugation.subgroupMap (U R (alpha R))).trans (MulEquiv.subgroupCongr frame.map_U)

@[simp] theorem movingEquiv_val (u : U R (alpha R)) :
    (frame.movingEquiv u : FreeAmalgam R) = frame.conjugation (u : FreeAmalgam R) := rfl

@[simp] theorem movingEquiv_symm_val (u : U R a) :
    frame.conjugation (frame.movingEquiv.symm u : FreeAmalgam R) = u := by
  rw [← movingEquiv_val, MulEquiv.apply_symm_apply]

theorem mem_fixedAt (x : FreeAmalgam R) :
    frame.conjugation x ∈ fixedAt R a ↔ x ∈ fixedPart R := by
  change frame.conjugation x ∈ X R a ∧
    frame.conjugation x ∈ centralizer (Ltilde R a : Set (FreeAmalgam R)) ↔ _
  rw [← frame.map_X, ← frame.map_Ltilde]
  change (frame.conjugation.toMonoidHom x ∈ (X R (alpha R)).map frame.conjugation.toMonoidHom ∧ _) ↔ _
  rw [mem_map_iff_mem frame.conjugation.injective]
  change (x ∈ X R (alpha R) ∧ _) ↔ (x ∈ X R (alpha R) ∧ _)
  apply and_congr_right
  intro _
  constructor
  · intro hx l hl
    apply frame.conjugation.injective
    simpa only [map_mul] using hx (frame.conjugation l) (mem_map_of_mem _ hl)
  · intro hx l hl
    obtain ⟨k, hk, rfl⟩ := hl
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg frame.conjugation (hx k hk)

theorem map_fixedPart : (fixedPart R).map frame.conjugation.toMonoidHom = fixedAt R a := by
  ext x
  obtain ⟨y, rfl⟩ := frame.conjugation.surjective x
  rw [frame.mem_fixedAt]
  exact mem_map_iff_mem frame.conjugation.injective

theorem unconjugate (g : M) (u v : U R a)
    (hv : (v : FreeAmalgam R) = (frame.localEquiv g : FreeAmalgam R) *
      (u : FreeAmalgam R) * (frame.localEquiv g : FreeAmalgam R)⁻¹) :
    (frame.movingEquiv.symm v : FreeAmalgam R) = embedM R g *
      (frame.movingEquiv.symm u : FreeAmalgam R) * (embedM R g)⁻¹ := by
  apply frame.conjugation.injective
  simpa only [map_mul, map_inv, movingEquiv_symm_val, localEquiv_val] using hv

end Frame

/-- Isomorphic moving copies with the full local conjugation action. -/
structure CopiesAt (source : LocalSource L R) (a : Vertex R) (frame : Frame R a) (m : ℕ) where
  marking : SL ≃* SL
  equiv : U R a ≃* Multiplicative (Fin m → Fin 3 → ZMod 2)
  action : ∀ (g : stabilizer R a) (u v : U R a),
    (v : FreeAmalgam R) = (g : FreeAmalgam R) * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
    ∀ i : Fin m, (equiv v).toAdd i =
      (marking (frame.projection source g)).val.mulVec ((equiv u).toAdd i)

/-- Surjective moving coordinates with the entire central kernel retained. -/
structure QuotientAt (source : LocalSource L R) (a : Vertex R) (frame : Frame R a) (m : ℕ) where
  marking : SL ≃* SL
  projection : U R a →* Multiplicative (Fin m → Fin 3 → ZMod 2)
  onto : Function.Surjective projection
  kernel : projection.ker = (fixedAt R a).subgroupOf (U R a)
  action : ∀ (g : stabilizer R a) (u v : U R a),
    (v : FreeAmalgam R) = (g : FreeAmalgam R) * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
    ∀ i : Fin m, (projection v).toAdd i =
      (marking (frame.projection source g)).val.mulVec ((projection u).toAdd i)

/-- The actual natural moving module, without forgetting invertibility. -/
structure NaturalAt (source : LocalSource L R) (a : Vertex R) (frame : Frame R a) where
  marking : SL ≃* SL
  equiv : U R a ≃* Multiplicative (Fin 3 → ZMod 2)
  action : ∀ (g : stabilizer R a) (u v : U R a),
    (v : FreeAmalgam R) = (g : FreeAmalgam R) * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
    (equiv v).toAdd = (marking (frame.projection source g)).val.mulVec ((equiv u).toAdd)

namespace Frame
variable {a : Vertex R} (frame : Frame R a) {source : LocalSource L R}

noncomputable def copies {m : ℕ} (model : MovingCopies source m) : CopiesAt source a frame m where
  marking := model.marking
  equiv := frame.movingEquiv.symm.trans model.equiv
  action := by
    intro g u v hv i
    obtain ⟨g, rfl⟩ := frame.localEquiv.surjective g
    simpa only [MulEquiv.trans_apply, projection_localEquiv] using
      model.action g _ _ (frame.unconjugate g u v hv) i

noncomputable def quotient {m : ℕ} (model : MovingQuotient source m) :
    QuotientAt source a frame m where
  marking := model.marking
  projection := model.projection.comp frame.movingEquiv.symm.toMonoidHom
  onto := model.onto.comp frame.movingEquiv.symm.surjective
  kernel := by
    ext u
    change model.projection (frame.movingEquiv.symm u) = 1 ↔
      (u : FreeAmalgam R) ∈ fixedAt R a
    rw [← frame.movingEquiv_symm_val u, frame.mem_fixedAt]
    exact show frame.movingEquiv.symm u ∈ model.projection.ker ↔
      (frame.movingEquiv.symm u : FreeAmalgam R) ∈ fixedPart R from by rw [model.kernel]; rfl
  action := by
    intro g u v hv i
    obtain ⟨g, rfl⟩ := frame.localEquiv.surjective g
    change (model.projection (frame.movingEquiv.symm v)).toAdd i =
      (model.marking (frame.projection source (frame.localEquiv g))).val.mulVec
        ((model.projection (frame.movingEquiv.symm u)).toAdd i)
    rw [projection_localEquiv]
    exact model.action g _ _ (frame.unconjugate g u v hv) i

noncomputable def natural (model : NaturalU R source.projection) : NaturalAt source a frame where
  marking := model.marking
  equiv := frame.movingEquiv.symm.trans model.equiv
  action := by
    intro g u v hv
    obtain ⟨g, rfl⟩ := frame.localEquiv.surjective g
    simpa only [MulEquiv.trans_apply, projection_localEquiv] using
      model.action g _ _ (frame.unconjugate g u v hv)

@[simp] theorem copies_marking {m : ℕ} (model : MovingCopies source m) :
    (frame.copies model).marking = model.marking := rfl

@[simp] theorem quotient_marking {m : ℕ} (model : MovingQuotient source m) :
    (frame.quotient model).marking = model.marking := rfl

@[simp] theorem natural_marking (model : NaturalU R source.projection) :
    (frame.natural model).marking = model.marking := rfl

end Frame

/-- Printed (3.2)(iii) at an arbitrary vertex, retaining the direct sum. -/
def SplitDoubleAt (source : LocalSource L R) (a : Vertex R) (frame : Frame R a) : Prop :=
  Nonempty (CopiesAt source a frame 2) ∧
    X R a = fixedAt R a ⊔ U R a ∧ Disjoint (fixedAt R a) (U R a)

/-- Printed (3.2)(iv), including the order-two overlap. -/
def CentralExtensionAt (source : LocalSource L R) (a : Vertex R) (frame : Frame R a) : Prop :=
  Nonempty (QuotientAt source a frame 1) ∧
    X R a = fixedAt R a ⊔ U R a ∧ Nat.card (fixedAt R a ⊓ U R a : Subgroup (FreeAmalgam R)) = 2

/-- Printed (3.2)(v), with Z rather than X as the direct sum. -/
def OuterExtensionAt (source : LocalSource L R) (a : Vertex R) (frame : Frame R a) : Prop :=
  Nonempty (NaturalAt source a frame) ∧
    Z R a = fixedAt R a ⊔ U R a ∧ Disjoint (fixedAt R a) (U R a) ∧
    (Z R a).relIndex (X R a) = 2

theorem splitDouble_at (source : LocalSource L R) (h : SplitDouble source)
    (a : Vertex R) (frame : Frame R a) : SplitDoubleAt source a frame := by
  obtain ⟨⟨model⟩, hsum, hd⟩ := h
  refine ⟨⟨frame.copies model⟩, ?_, ?_⟩
  · have he := congrArg (Subgroup.map frame.conjugation.toMonoidHom) hsum
    simpa only [Subgroup.map_sup, frame.map_X, frame.map_U, frame.map_fixedPart] using he
  · simpa only [frame.map_U, frame.map_fixedPart] using
      (Subgroup.disjoint_map (f := frame.conjugation.toMonoidHom) frame.conjugation.injective hd)

theorem centralExtension_at (source : LocalSource L R) (h : CentralExtension source)
    (a : Vertex R) (frame : Frame R a) : CentralExtensionAt source a frame := by
  obtain ⟨⟨model⟩, hsum, hk⟩ := h
  refine ⟨⟨frame.quotient model⟩, ?_, ?_⟩
  · have he := congrArg (Subgroup.map frame.conjugation.toMonoidHom) hsum
    simpa only [Subgroup.map_sup, frame.map_X, frame.map_U, frame.map_fixedPart] using he
  · have he := Nat.card_congr
      (frame.conjugation.subgroupMap (fixedPart R ⊓ U R (alpha R))).toEquiv
    change Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) =
      Nat.card ((fixedPart R ⊓ U R (alpha R)).map frame.conjugation.toMonoidHom) at he
    rw [Subgroup.map_inf _ _ _ frame.conjugation.injective,
      frame.map_fixedPart, frame.map_U] at he
    exact he.symm.trans hk

theorem outerExtension_at (source : LocalSource L R) (h : OuterExtension source)
    (a : Vertex R) (frame : Frame R a) : OuterExtensionAt source a frame := by
  obtain ⟨⟨model⟩, hsum, hd, hi⟩ := h
  refine ⟨⟨frame.natural model⟩, ?_, ?_, ?_⟩
  · have he := congrArg (Subgroup.map frame.conjugation.toMonoidHom) hsum
    simpa only [Subgroup.map_sup, frame.map_Z, frame.map_U, frame.map_fixedPart] using he
  · simpa only [frame.map_U, frame.map_fixedPart] using
      (Subgroup.disjoint_map (f := frame.conjugation.toMonoidHom) frame.conjugation.injective hd)
  · have he := relIndex_map_map_of_injective (f := frame.conjugation.toMonoidHom)
      (Z R (alpha R)) (X R (alpha R)) frame.conjugation.injective
    rw [frame.map_Z, frame.map_X] at he
    exact he.trans hi

theorem CopiesAt.card_two {source : LocalSource L R} {a : Vertex R} {frame : Frame R a}
    (model : CopiesAt source a frame 2) : Nat.card (U R a) = 64 := by
  rw [Nat.card_congr model.equiv.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

theorem QuotientAt.card_one {source : LocalSource L R} {a : Vertex R} {frame : Frame R a}
    (model : QuotientAt source a frame 1)
    (hk : Nat.card (fixedAt R a ⊓ U R a : Subgroup (FreeAmalgam R)) = 2) :
    Nat.card (U R a) = 16 := by
  have hker : Nat.card model.projection.ker = 2 := by
    rw [model.kernel]
    let e : (fixedAt R a).subgroupOf (U R a) ≃*
        (fixedAt R a ⊓ U R a : Subgroup (FreeAmalgam R)) :=
      (MulEquiv.subgroupCongr (inf_subgroupOf_right _ _).symm).trans
        (subgroupOfEquivOfLe inf_le_right)
    exact (Nat.card_congr e.toEquiv).trans hk
  have hsize := model.projection.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr model.onto,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hker] at hsize
  norm_num [Nat.card_eq_fintype_card] at hsize
  exact hsize.symm

theorem NaturalAt.card {source : LocalSource L R} {a : Vertex R} {frame : Frame R a}
    (model : NaturalAt source a frame) : Nat.card (U R a) = 8 := by
  rw [Nat.card_congr model.equiv.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

variable [Finite M]

/-- Both branches whose direct sum is X have X = Z at every source vertex. -/
theorem X_eq_Z_of_sum (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (hsum : X R a = fixedAt R a ⊔ U R a) : X R a = Z R a := by
  apply le_antisymm
  · rw [hsum]
    exact sup_le (source.X_fixed_le_Z a ha) (U_le_Z a)
  · apply geometry.omega_bound a ha
    rw [geometry.distance_constant a ha]
    exact hb

theorem splitDouble_X_eq_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) : X R a = Z R a := by
  obtain ⟨frame⟩ := exists_frame a ha
  exact X_eq_Z_of_sum source geometry hb a ha (splitDouble_at source h a frame).2.1

theorem centralExtension_X_eq_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : CentralExtension source)
    (a : Vertex R) (ha : color R a = false) : X R a = Z R a := by
  obtain ⟨frame⟩ := exists_frame a ha
  exact X_eq_Z_of_sum source geometry hb a ha (centralExtension_at source h a frame).2.1

/-- In the doubled branch the literal source quotient and the auxiliary
quotient coincide, at a critical pair as well as at any two source vertices. -/
theorem splitDouble_commutator_eq (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : SplitDouble source)
    (a a' : Vertex R) (ha : color R a = false) (ha' : color R a' = false) :
    ⁅Z R a, Z R a'⁆ = ⁅X R a, X R a'⁆ := by
  rw [splitDouble_X_eq_Z source geometry hb h a ha,
    splitDouble_X_eq_Z source geometry hb h a' ha']

/-- The same identification holds in the nonsplit central extension. -/
theorem centralExtension_commutator_eq (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : CentralExtension source)
    (a a' : Vertex R) (ha : color R a = false) (ha' : color R a' = false) :
    ⁅Z R a, Z R a'⁆ = ⁅X R a, X R a'⁆ := by
  rw [centralExtension_X_eq_Z source geometry hb h a ha,
    centralExtension_X_eq_Z source geometry hb h a' ha']

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation
