module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.AmbientFusion
public import Theory.GroupTheory.DihedralProductTransfer

/-!
# Original wreath coordinates on the t-centralizer Sylow

The original marking embeds the ordered dihedral product into G. Its range
is exactly the elementary Thompson subgroup, and vanishing of each coordinate
means membership in the other original factor Sylow. The already proved
Sylow theorem in C_G(t) therefore gives a multiplicative equivalence that
retains this literal embedding. No conjugation changes either factor.

Source: Aschbacher–Smith 13.9.2 and the proof of 13.9.5, pp.969–971.
-/


@[expose] public noncomputable section
open Subgroup SymmetricFourWreath
namespace CFSG.Quasithin.Chapter13.Section09.Marking
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

def baseProductEmbedding : D8×D8 →* G := m.embedding.comp (sylowEmbedding.comp pair)

theorem baseProductEmbedding_injective : Function.Injective m.baseProductEmbedding :=
  m.embedding_injective.comp (sylowEmbedding_injective.comp pair_injective)

theorem range_baseProductEmbedding : m.baseProductEmbedding.range=m.dihedralBase := by
  change (m.embedding.comp (sylowEmbedding.comp pair)).range = (pair.range.map sylowEmbedding).map m.embedding
  rw [MonoidHom.range_comp,MonoidHom.range_comp]

theorem baseProductEmbedding_mem_sylow (a b : D8) :
    m.baseProductEmbedding (a,b) ∈ (d.T : Subgroup G) := by
  rw [←m.image_standardSylow]
  exact mem_map_of_mem _ ⟨pair (a,b),rfl⟩

theorem baseProductEmbedding_axis : m.baseProductEmbedding (DihedralGroup.r 2,1)=m.t := by
  change m.embedding (sylowEmbedding (pair (DihedralGroup.r 2,1))) = m.t
  rw [sylowEmbedding_axis]
  rfl

private theorem native_first (a : D8) : sylowEmbedding (pair (a,1))=SymmetricFourWreath.factor 1 (square a) := by
  apply RegularWreathProduct.ext
  · funext i
    by_cases hi:i=1 <;> simp [sylowEmbedding,pair,SymmetricFourWreath.factor,hi]
  · rfl
private theorem native_second (b : D8) : sylowEmbedding (pair (1,b))=SymmetricFourWreath.factor turn (square b) := by
  apply RegularWreathProduct.ext
  · funext i
    rcases c2_eq_one_or_turn i with rfl|rfl <;>
      simp [sylowEmbedding,pair,SymmetricFourWreath.factor,turn_ne_one,Ne.symm turn_ne_one]
  · rfl

theorem baseProductEmbedding_mem_first (a b : D8) :
    m.baseProductEmbedding (a,b)∈m.factorSylow 1 ↔ b=1 := by
  constructor
  · rintro ⟨_,⟨_,⟨w,rfl⟩,hh⟩⟩
    have he : SymmetricFourWreath.factor 1 w=sylowEmbedding (pair (a,b)) := m.embedding_injective hh
    have ht := congrArg (fun v:W=>v.left turn) he
    have hb : square b=1 := by
      simpa [SymmetricFourWreath.factor,sylowEmbedding,pair,turn_ne_one] using ht.symm
    exact square_injective (hb.trans (map_one square).symm)
  · rintro rfl
    refine ⟨m.baseProductEmbedding_mem_sylow a 1, ?_⟩
    exact ⟨SymmetricFourWreath.factor 1 (square a),⟨square a,rfl⟩,
      congrArg m.embedding (native_first a).symm⟩

theorem baseProductEmbedding_mem_second (a b : D8) :
    m.baseProductEmbedding (a,b)∈m.factorSylow turn ↔ a=1 := by
  constructor
  · rintro ⟨_,⟨_,⟨w,rfl⟩,hh⟩⟩
    have he : SymmetricFourWreath.factor turn w=sylowEmbedding (pair (a,b)) := m.embedding_injective hh
    have ht := congrArg (fun v:W=>v.left 1) he
    have ha : square a=1 := by
      simpa [SymmetricFourWreath.factor,sylowEmbedding,pair,Ne.symm turn_ne_one] using ht.symm
    exact square_injective (ha.trans (map_one square).symm)
  · rintro rfl
    refine ⟨m.baseProductEmbedding_mem_sylow 1 b, ?_⟩
    exact ⟨SymmetricFourWreath.factor turn (square b),⟨square b,rfl⟩,
      congrArg m.embedding (native_second b).symm⟩

/-- Each of the literal factor Sylows lies in the dihedral base. -/
theorem factorSylow_le_dihedralBase (i:C2) : m.factorSylow i≤m.dihedralBase := by
  intro x hx
  have hxT := hx.1
  rw [←m.image_standardSylow] at hxT
  obtain ⟨w,hw,he⟩ := hxT
  obtain ⟨_,⟨a,rfl⟩,ha⟩ := hx.2
  have hwa : w=SymmetricFourWreath.factor i a := m.embedding_injective (he.trans ha.symm)
  refine ⟨w,(mem_J w).mpr ⟨?_,(mem_standardSylow w).mp hw⟩,he⟩
  rw [hwa]
  rfl

variable (S : Sylow 2 (centralizer ({m.t}:Set G)))
  (hS : (S : Subgroup (centralizer ({m.t}:Set G))).map
    (centralizer ({m.t}:Set G)).subtype=m.dihedralBase)

def baseProductToSylow : D8×D8 →* S :=
  let f := m.baseProductEmbedding.codRestrict (centralizer ({m.t}:Set G)) (fun ab => by
    have hh : m.baseProductEmbedding ab∈m.dihedralBase :=
      m.range_baseProductEmbedding ▸ (show m.baseProductEmbedding ab∈m.baseProductEmbedding.range from ⟨ab,rfl⟩)
    rw [←hS] at hh
    exact map_subtype_le _ hh)
  f.codRestrict (S:Subgroup (centralizer ({m.t}:Set G))) (fun ab => by
    have hh : m.baseProductEmbedding ab∈m.dihedralBase :=
      m.range_baseProductEmbedding ▸ (show m.baseProductEmbedding ab∈m.baseProductEmbedding.range from ⟨ab,rfl⟩)
    rw [←hS] at hh
    obtain ⟨x,hx,he⟩ := hh
    have he' : x=f ab := Subtype.ext he
    exact he' ▸ hx)

theorem baseProductToSylow_bijective : Function.Bijective (m.baseProductToSylow S hS) := by
  refine ⟨fun a b h=>m.baseProductEmbedding_injective (congrArg (fun x:S=>((x : centralizer ({m.t}:Set G)):G)) h),?_⟩
  intro x
  have hx : ((x:centralizer ({m.t}:Set G)):G)∈m.baseProductEmbedding.range := by
    rw [m.range_baseProductEmbedding,←hS]
    exact mem_map_of_mem _ x.property
  obtain ⟨ab,hab⟩ := hx
  exact ⟨ab,Subtype.ext (Subtype.ext hab)⟩

def baseProductSylowEquiv : S ≃* D8×D8 :=
  (MulEquiv.ofBijective (m.baseProductToSylow S hS) (m.baseProductToSylow_bijective S hS)).symm

theorem baseProductSylowEquiv_symm_coe (ab:D8×D8) :
    (((m.baseProductSylowEquiv S hS).symm ab:S):centralizer ({m.t}:Set G)) =
      ⟨m.baseProductEmbedding ab,(m.baseProductToSylow S hS ab).val.property⟩ := rfl
end CFSG.Quasithin.Chapter13.Section09.Marking
