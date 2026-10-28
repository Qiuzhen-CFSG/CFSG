module

public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients.Numbering
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.StandardPair
public import Theory.AtlasPort.LinearGroups.G2.LieCoreSpecialness
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# The marked binary G₂ exceptional models in F.1.12

Both models use the actual split-octonion parabolics and their whole common
Sylow subgroup. In G₂(2)′ these are restrictions to the literal commutator
subgroup. The local factors Lᵢ equal the parabolics in these binary models;
the equalities with the literal products LᵢB and LᵢS are proved below.

The derived quotients are PSL₂(2), with cores Q₈ ◦ C₄ and C₄ × C₄.
The full group has the special first core of order 32 and center order two,
and second core of order 32. Conjugation identifies this same full model
with Aut(G₂(2)′) and transports the entire inclusion amalgam, including
both squares and the embedded inner group. The predicates for recognition
are indexed by these concrete amalgams; no uniqueness claim is assumed.

Source: Aschbacher--Smith, F.1.11--12, printed pp.262--264 (PDF pp.273--275),
with the marked restriction from 14.2.21, printed p.988. The imported concrete
root calculations carry the ATLAS attribution in LICENSES/ATLAS.txt.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.ExceptionalModels.G2

open Theory.GroupTheory Atlas.G2 Atlas.G2.BinaryParabolicPair
open Atlas.G2.BinaryCore Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
open Atlas.G2.ExceptionalLocalQuotients
open scoped Pointwise MatrixGroups

abbrev Full := Model (ZMod 2)
abbrev Derived := DerivedModel

abbrev fullL₁ : Subgroup Full := firstParabolic
abbrev fullL₂ : Subgroup Full := secondParabolic
abbrev fullS : Sylow 2 Full := commonSylow
abbrev fullB : Subgroup Full := (fullS : Subgroup Full)

abbrev derivedL₁ : Subgroup Derived := derivedFirst
abbrev derivedL₂ : Subgroup Derived := derivedSecond
abbrev derivedS : Sylow 2 Derived := derivedSylow
abbrev derivedB : Subgroup Derived := (derivedS : Subgroup Derived)

/-- B is the whole overlap, not a proper subgroup chosen inside it. -/
theorem full_overlap : fullL₁ ⊓ fullL₂ = fullB := parabolic_intersection

theorem derived_overlap : derivedL₁ ⊓ derivedL₂ = derivedB :=
  derived_parabolic_intersection_in_model

private theorem product_of_le {G : Type*} [Group G] {P S : Subgroup G} (h : S ≤ P) :
    (P : Set G) * (S : Set G) = (P : Set G) := by
  ext g
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact P.mul_mem hx (h hy)
  · intro hg
    exact ⟨g,hg,1,S.one_mem,mul_one g⟩

/-- At q=2 the full parabolics are literally LᵢB = LᵢS = Lᵢ. -/
theorem full_products :
    (fullL₁ : Set Full) * (fullB : Set Full) = fullL₁ ∧
    (fullL₂ : Set Full) * (fullB : Set Full) = fullL₂ :=
  ⟨product_of_le commonSylow_le_first, product_of_le commonSylow_le_second⟩

/-- The same literal-product assertions hold in the actual derived group. -/
theorem derived_products :
    (derivedL₁ : Set Derived) * (derivedB : Set Derived) = derivedL₁ ∧
    (derivedL₂ : Set Derived) * (derivedB : Set Derived) = derivedL₂ :=
  ⟨product_of_le derivedSylow_le_first, product_of_le derivedSylow_le_second⟩

abbrev fullAmalgam : RankTwoAmalgam fullL₁ fullB fullL₂ := concreteAmalgam
abbrev simpleAmalgam : RankTwoAmalgam derivedL₁ derivedB derivedL₂ := derivedAmalgam

theorem full_embeddings : Function.Injective fullAmalgam.left ∧
    Function.Injective fullAmalgam.right :=
  ⟨Subgroup.inclusion_injective commonSylow_le_first,
    Subgroup.inclusion_injective commonSylow_le_second⟩

theorem derived_embeddings : Function.Injective simpleAmalgam.left ∧
    Function.Injective simpleAmalgam.right :=
  ⟨Subgroup.inclusion_injective derivedSylow_le_first,
    Subgroup.inclusion_injective derivedSylow_le_second⟩

/-- The existing root-geometric comparison respects both overlap maps. -/
def fullGeometricIso : RankTwoAmalgam.Iso fullAmalgam geometricPair := geometricPairIso

def derivedGeometricIso : RankTwoAmalgam.Iso simpleAmalgam derivedGeometricPair :=
  derivedGeometricPairIso

/-- The inclusion amalgams have their stated ambient groups as completions. -/
theorem full_generation : fullL₁ ⊔ fullL₂ = ⊤ := by
  change firstParabolic ⊔ parabolic = ⊤
  rw [← parabolic₁_binary]
  exact parabolics_generate

theorem derived_generation : derivedL₁ ⊔ derivedL₂ = ⊤ := by
  change firstParabolic.subgroupOf Derived ⊔ secondParabolic.subgroupOf Derived = ⊤
  rw [← parabolic₁_binary]
  exact binaryMarkedParabolic_sup

/-- These are the actual restrictions of the full pair to its commutator. -/
theorem derived_marking :
    derivedL₁ = fullL₁.subgroupOf Derived ∧
    derivedL₂ = fullL₂.subgroupOf Derived ∧
    derivedB = fullB.subgroupOf Derived :=
  ⟨rfl, rfl, derivedSylow_eq⟩

/-- The left intrinsic core, with S adjoined exactly as in the source. -/
def derivedFirstSylowCoreEquiv :
    pCore 2 (derivedL₁ ⊔ (derivedS : Subgroup Derived) : Subgroup Derived) ≃* QuaternionCyclic.Model :=
  (LocalCoreTransport.coreEquiv 2
    (MulEquiv.subgroupCongr (sup_eq_left.mpr derivedSylow_le_first))).trans
      derivedIntrinsicCoreEquiv

def derivedSecondSylowCoreEquiv :
    pCore 2 (derivedL₂ ⊔ (derivedS : Subgroup Derived) : Subgroup Derived) ≃* C4Square :=
  (LocalCoreTransport.coreEquiv 2
    (MulEquiv.subgroupCongr (sup_eq_left.mpr derivedSylow_le_second))).trans
      derivedSecondCoreEquiv

/-- The first derived local centralizes the full Sylow center, fixing the source labels. -/
theorem derived_numbering :
    ⁅derivedL₁, (Subgroup.center (derivedS : Subgroup Derived)).map
      (derivedS : Subgroup Derived).subtype⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨x,hx,rfl⟩
  exact derivedFirst_centralizes_sylow_center ⟨x,hx⟩ ⟨g,hg⟩

/-- All local identifications in the concrete F.1.12(I)(8) model. -/
theorem source_I_8 :
    Nonempty (RankTwoAmalgam.Iso simpleAmalgam derivedGeometricPair) ∧
    Nonempty ((derivedL₁ ⧸ pCore 2 derivedL₁) ≃* PSL(2,ZMod 2)) ∧
    Nonempty ((derivedL₂ ⧸ pCore 2 derivedL₂) ≃* PSL(2,ZMod 2)) ∧
    Nonempty (pCore 2 (derivedL₁ ⊔ (derivedS : Subgroup Derived) : Subgroup Derived) ≃*
      QuaternionCyclic.Model) ∧
    Nonempty (pCore 2 (derivedL₂ ⊔ (derivedS : Subgroup Derived) : Subgroup Derived) ≃* C4Square) ∧
    ⁅derivedL₁, (Subgroup.center (derivedS : Subgroup Derived)).map
      (derivedS : Subgroup Derived).subtype⁆ = ⊥ :=
  ⟨⟨derivedGeometricIso⟩, ⟨derivedFirstQuotientEquiv⟩, ⟨derivedSecondQuotientEquiv⟩,
    ⟨derivedFirstSylowCoreEquiv⟩, ⟨derivedSecondSylowCoreEquiv⟩, derived_numbering⟩

def fullFirstQuotientEquiv : fullL₁ ⧸ pCore 2 fullL₁ ≃* PSL(2,ZMod 2) :=
  (LocalCoreTransport.quotientEquiv 2 (MulEquiv.subgroupCongr local₁_binary.symm)).trans
    local₁CoreQuotientEquivPSL

def fullSecondQuotientEquiv : fullL₂ ⧸ pCore 2 fullL₂ ≃* PSL(2,ZMod 2) :=
  (LocalCoreTransport.quotientEquiv 2 (MulEquiv.subgroupCongr local₂_binary.symm)).trans
    local₂CoreQuotientEquivPSL

/-- The full first intrinsic core retains the original five-root embedding. -/
def fullFirstCoreEquiv : pCore 2 fullL₁ ≃* core :=
  (LocalCoreTransport.coreEquiv 2 (MulEquiv.subgroupCongr local₁_binary.symm)).trans
    (local₁_binary_coreEquiv.trans (MulEquiv.subgroupCongr radical₁_binary))

/-- Notation F.1.11's complete special-group meaning, including nonabelianness. -/
theorem full_first_special :
    let Q := pCore 2 (fullL₁ ⊔ (fullS : Subgroup Full) : Subgroup Full)
    IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
    commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
    IsElementaryAbelian 2 (Subgroup.center Q) ∧ Nat.card Q = 32 ∧
    Nat.card (Subgroup.center Q) = 2 := by
  dsimp only
  rw [sup_eq_left.mpr commonSylow_le_first, ← local₁_binary]
  have h := local₁_pCore_special (F := ZMod 2)
  norm_num only [Nat.card_eq_fintype_card, ZMod.card] at h
  exact h

theorem full_second_core_card :
    Nat.card (pCore 2 (fullL₂ ⊔ (fullS : Subgroup Full) : Subgroup Full)) = 32 := by
  rw [sup_eq_left.mpr commonSylow_le_second, ← local₂_binary]
  exact card_local₂_pCore_binary

/-- The prescribed source numbering uses the whole Sylow center. -/
theorem full_numbering :
    ⁅fullL₁, (Subgroup.center (fullS : Subgroup Full)).map
      (fullS : Subgroup Full).subtype⁆ = ⊥ :=
  local₁_commutator_sylow_center (F := ZMod 2)

/-- The full binary model realizes the q=2 instance of F.1.12(I)(3). -/
theorem source_I_3 :
    Nonempty (RankTwoAmalgam.Iso fullAmalgam geometricPair) ∧
    Nonempty ((fullL₁ ⧸ pCore 2 fullL₁) ≃* PSL(2,ZMod 2)) ∧
    Nonempty ((fullL₂ ⧸ pCore 2 fullL₂) ≃* PSL(2,ZMod 2)) ∧
    (let Q := pCore 2 (fullL₁ ⊔ (fullS : Subgroup Full) : Subgroup Full);
      IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧ commutator Q = Subgroup.center Q ∧
      frattini Q = Subgroup.center Q ∧ IsElementaryAbelian 2 (Subgroup.center Q) ∧
      Nat.card Q = 32 ∧ Nat.card (Subgroup.center Q) = 2) ∧
    Nat.card (pCore 2 (fullL₂ ⊔ (fullS : Subgroup Full) : Subgroup Full)) = 32 :=
  ⟨⟨fullGeometricIso⟩, ⟨fullFirstQuotientEquiv⟩, ⟨fullSecondQuotientEquiv⟩,
    full_first_special, full_second_core_card⟩

/-- The extension identification is pointwise ambient conjugation. -/
def automorphismEquiv : Full ≃* MulAut Derived := binaryAutomorphismEquiv

@[simp] theorem automorphismEquiv_apply (g : Full) (x : Derived) :
    (automorphismEquiv g x).val = g * x.val * g⁻¹ := binaryAutomorphismEquiv_apply_val g x

/-- Its restriction to the actual commutator is the inner automorphism map. -/
theorem automorphismEquiv_inner (x : Derived) :
    automorphismEquiv x.val = MulAut.conj x := binaryConjugation_inner x

def autL₁ : Subgroup (MulAut Derived) := fullL₁.map automorphismEquiv.toMonoidHom
def autL₂ : Subgroup (MulAut Derived) := fullL₂.map automorphismEquiv.toMonoidHom
def autB : Subgroup (MulAut Derived) := fullB.map automorphismEquiv.toMonoidHom

def automorphismAmalgam : RankTwoAmalgam autL₁ autB autL₂ :=
  .ofSubgroups _ _ _ (Subgroup.map_mono commonSylow_le_first)
    (Subgroup.map_mono commonSylow_le_second)

/-- The full parabolics, their whole overlap, and both maps extend together. -/
def automorphismAmalgamIso : RankTwoAmalgam.Iso fullAmalgam automorphismAmalgam :=
  RankTwoAmalgam.ofSubgroupsIso automorphismEquiv commonSylow_le_first commonSylow_le_second
    (Subgroup.map_mono commonSylow_le_first) (Subgroup.map_mono commonSylow_le_second)
    rfl rfl rfl

theorem automorphism_overlap : autL₁ ⊓ autL₂ = autB := by
  rw [autL₁, autL₂, autB, ← Subgroup.map_inf fullL₁ fullL₂ automorphismEquiv.toMonoidHom automorphismEquiv.injective, full_overlap]

/-- Actual model predicates for recognition; existence of an isomorphism is not asserted
for arbitrary amalgams. Both commuting squares are part of each predicate. -/
def IsDerivedAmalgam {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) : Prop := Nonempty (RankTwoAmalgam.Iso α simpleAmalgam)

def IsFullAmalgam {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) : Prop := Nonempty (RankTwoAmalgam.Iso α fullAmalgam)

/-- The local conclusions transported to any compatibly identified derived amalgam. -/
theorem IsDerivedAmalgam.local_structure {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (h : IsDerivedAmalgam α) :
    Nonempty ((L ⧸ pCore 2 L) ≃* PSL(2,ZMod 2)) ∧
    Nonempty ((R ⧸ pCore 2 R) ≃* PSL(2,ZMod 2)) ∧
    Nonempty (pCore 2 L ≃* QuaternionCyclic.Model) ∧
    Nonempty (pCore 2 R ≃* C4Square) := by
  obtain ⟨e⟩ := h
  exact ⟨⟨(e.toParabolicEquiv.leftCoreQuotientEquiv 2).trans derivedFirstQuotientEquiv⟩,
    ⟨(e.toParabolicEquiv.rightCoreQuotientEquiv 2).trans derivedSecondQuotientEquiv⟩,
    ⟨(LocalCoreTransport.coreEquiv 2 e.left).trans derivedIntrinsicCoreEquiv⟩,
    ⟨(LocalCoreTransport.coreEquiv 2 e.right).trans derivedSecondCoreEquiv⟩⟩

/-- Full-model local data also transport through the actual compatible maps. -/
theorem IsFullAmalgam.local_structure {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (h : IsFullAmalgam α) :
    Nonempty ((L ⧸ pCore 2 L) ≃* PSL(2,ZMod 2)) ∧
    Nonempty ((R ⧸ pCore 2 R) ≃* PSL(2,ZMod 2)) ∧
    Nonempty (pCore 2 L ≃* core) ∧ Nat.card (pCore 2 R) = 32 := by
  obtain ⟨e⟩ := h
  refine ⟨⟨(e.toParabolicEquiv.leftCoreQuotientEquiv 2).trans fullFirstQuotientEquiv⟩,
    ⟨(e.toParabolicEquiv.rightCoreQuotientEquiv 2).trans fullSecondQuotientEquiv⟩,
    ⟨(LocalCoreTransport.coreEquiv 2 e.left).trans fullFirstCoreEquiv⟩, ?_⟩
  rw [LocalCoreTransport.core_card 2 e.right]
  have h := full_second_core_card
  rwa [sup_eq_left.mpr commonSylow_le_second] at h

/-- The literal automorphism-group amalgam realizes the full model predicate. -/
theorem automorphism_isFullAmalgam : IsFullAmalgam automorphismAmalgam :=
  ⟨automorphismAmalgamIso.symm⟩

end CFSG.Quasithin.ChapterF.GreenBook.ExceptionalModels.G2
end
