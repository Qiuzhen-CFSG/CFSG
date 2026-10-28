module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.ResidualFusion.Coordinates
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Sylow
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The original four-group used in the terminal construction

The first normal dihedral four-plane is exactly T₁ ∩ O₂(M) and O₂(M₁),
through the fixed embedding of the original configuration. Its centralizer
in J(T)=T₁×T₂ is the internal direct product E×T₂. All coordinate identities
are proved in the two eight-element dihedral factors, then transported through
the actual marking. These supply the Sylow product for O²(C_G(E)).
Source: Aschbacher--Smith, 13.9.10 and proof of 13.9.1, pp.973--974.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

def terminalFour : Subgroup G := ((plane true).prod ⊥).map m.baseProductEmbedding

theorem terminalFour_le_base : m.terminalFour ≤ m.dihedralBase := by
  rw [←m.range_baseProductEmbedding]
  exact map_le_range _ _

theorem terminalFour_coordinate (a b:D8) :
    m.baseProductEmbedding (a,b)∈m.terminalFour ↔ a∈plane true ∧ b=1 := by
  change m.baseProductEmbedding (a,b)∈((plane true).prod ⊥).map m.baseProductEmbedding ↔ _
  rw [mem_map_iff_mem m.baseProductEmbedding_injective]
  rfl

theorem elementaryGroup_coordinate (a b:D8) (c e:Bool) :
    m.baseProductEmbedding (a,b)∈m.elementaryGroup c e ↔ a∈plane c ∧ b∈plane e := by
  change m.baseProductEmbedding (a,b)∈((((plane c).prod (plane e)).map pair).map sylowEmbedding).map m.embedding ↔ _
  rw [map_map,map_map]
  exact mem_map_iff_mem m.baseProductEmbedding_injective

theorem terminalFour_eq_source :
    m.terminalFour=m.factorSylow 1 ⊓ m.elementaryGroup true true := by
  ext x
  constructor
  · intro hx
    have hxJ:=m.terminalFour_le_base hx
    rw [←m.range_baseProductEmbedding] at hxJ
    obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
    obtain ⟨ha,rfl⟩:=(m.terminalFour_coordinate a b).mp hx
    exact ⟨(m.baseProductEmbedding_mem_first a 1).mpr rfl,
      (m.elementaryGroup_coordinate a 1 true true).mpr ⟨ha,(plane true).one_mem⟩⟩
  · intro hx
    have hxJ:=m.factorSylow_le_dihedralBase 1 hx.1
    rw [←m.range_baseProductEmbedding] at hxJ
    obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
    exact (m.terminalFour_coordinate a b).mpr
      ⟨((m.elementaryGroup_coordinate a b true true).mp hx.2).1,
        (m.baseProductEmbedding_mem_first a b).mp hx.1⟩

instance terminalFour_elementary : IsElementaryAbelian 2 m.terminalFour := by
  rw [m.terminalFour_eq_source]
  exact IsElementaryAbelian.of_le inf_le_right


theorem t_mem_terminalFour : m.t∈m.terminalFour := by
  rw [←m.baseProductEmbedding_axis]
  exact (m.terminalFour_coordinate _ _).mpr ⟨by decide,rfl⟩

theorem base_normalizes_terminalFour : m.dihedralBase≤normalizer (m.terminalFour:Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  rw [←m.range_baseProductEmbedding] at hg
  obtain ⟨⟨a,b⟩,rfl⟩:=hg
  obtain ⟨⟨c,e⟩,⟨hc,he⟩,rfl⟩:=hx
  change e=1 at he
  subst e
  rw [←map_inv,←map_mul,←map_mul]
  change m.baseProductEmbedding (a*c*a⁻¹,b*1*b⁻¹)∈_
  rw [mul_one,mul_inv_cancel]
  exact (m.terminalFour_coordinate _ _).mpr
    ⟨(by decide : ∀a c:D8,c∈plane true→a*c*a⁻¹∈plane true) a c hc,rfl⟩

theorem base_centralizer_terminalFour (a b:D8) :
    m.baseProductEmbedding (a,b)∈centralizer (m.terminalFour:Set G) ↔ a∈plane true := by
  rw [mem_centralizer_iff]
  constructor
  · intro h
    have hcomm : ∀c:D8,c∈plane true→c*a=a*c := by
      intro c hc
      have he:=h (m.baseProductEmbedding (c,1)) ((m.terminalFour_coordinate c 1).mpr ⟨hc,rfl⟩)
      rw [←map_mul,←map_mul] at he
      have hp:=m.baseProductEmbedding_injective he
      exact congrArg Prod.fst hp
    exact (by decide : ∀a:D8,(∀c:D8,c∈plane true→c*a=a*c)→a∈plane true) a hcomm
  · intro ha x hx
    obtain ⟨⟨c,e⟩,⟨hc,he⟩,rfl⟩:=hx
    change e=1 at he
    subst e
    rw [←map_mul,←map_mul]
    apply congrArg m.baseProductEmbedding
    exact Prod.ext
      ((by decide : ∀a c:D8,a∈plane true→c∈plane true→c*a=a*c) a c ha hc)
      (by simp)

theorem terminalFour_disjoint_second : Disjoint m.terminalFour (m.factorSylow turn) := by
  apply disjoint_def.mpr
  intro x hx hy
  obtain ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩:=hx
  have ha1: a=1:=(m.baseProductEmbedding_mem_second a b).mp hy
  change b=1 at hb
  rw [ha1,hb]
  exact map_one m.baseProductEmbedding

theorem terminalFour_commutes_second : m.terminalFour≤centralizer (m.factorSylow turn:Set G) := by
  apply le_centralizer_iff.mpr
  intro x hx
  have hxJ:=m.factorSylow_le_dihedralBase turn hx
  rw [←m.range_baseProductEmbedding] at hxJ
  obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
  have ha: a=1:=(m.baseProductEmbedding_mem_second a b).mp hx
  subst a
  exact (m.base_centralizer_terminalFour 1 b).mpr (plane true).one_mem

theorem base_inf_centralizer_terminalFour :
    m.dihedralBase⊓centralizer (m.terminalFour:Set G)=m.terminalFour⊔m.factorSylow turn := by
  apply le_antisymm
  · intro x hx
    have hxJ:=hx.1
    rw [←m.range_baseProductEmbedding] at hxJ
    obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
    have ha: a∈plane true:=(m.base_centralizer_terminalFour a b).mp hx.2
    have h1: m.baseProductEmbedding (a,1)∈m.terminalFour :=
      (m.terminalFour_coordinate a 1).mpr ⟨ha,rfl⟩
    have h2: m.baseProductEmbedding (1,b)∈m.factorSylow turn :=
      (m.baseProductEmbedding_mem_second 1 b).mpr rfl
    simpa only [←map_mul,Prod.mk_mul_mk,mul_one,one_mul] using
      (m.terminalFour⊔m.factorSylow turn).mul_mem (mem_sup_left h1) (mem_sup_right h2)
  · apply sup_le
    · refine le_inf m.terminalFour_le_base ?_
      exact le_centralizer_iff_isMulCommutative.mpr inferInstance
    · exact le_inf (m.factorSylow_le_dihedralBase turn)
        (le_centralizer_iff.mp m.terminalFour_commutes_second)


private theorem first_axis (a:D8) : m.baseProductEmbedding (a,1)=
    m.embedding (SymmetricFourWreath.factor 1 (square a)) := by
  apply congrArg m.embedding
  apply RegularWreathProduct.ext
  · funext i
    by_cases hi:i=1 <;> simp [sylowEmbedding,pair,SymmetricFourWreath.factor,hi]
  · rfl

private theorem plane_true_core : (plane true).map square=pCore 2 S4 := by
  rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
  ext x
  exact (by decide : ∀x:S4,(∃a:D8,a∈plane true ∧ square a=x) ↔
    x∈Theory.SpecificGroups.SymmetricSix.DuadCalculation.core) x

theorem terminalFour_eq_factorCore : m.terminalFour=(m.factor 1).pCoreIn 2 := by
  let f:=m.embedding.comp (SymmetricFourWreath.factor 1)
  have hf:f.range=m.factor 1 := by rw [MonoidHom.range_comp]; rfl
  rw [←hf,pCoreIn_range_of_injective 2 f (m.embedding_injective.comp (factor_injective 1)),
    ←plane_true_core,map_map]
  ext x
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    change b=1 at hb
    subst b
    exact ⟨a,ha,(m.first_axis a).symm⟩
  · rintro ⟨a,ha,rfl⟩
    rw [show (f.comp square) a=m.baseProductEmbedding (a,1) from (m.first_axis a).symm]
    exact (m.terminalFour_coordinate a 1).mpr ⟨ha,rfl⟩

theorem terminalFour_eq_original_core :
    m.terminalFour=m.factorSylow 1 ⊓ d.M.pCoreIn 2 := by
  rw [m.terminalFour_eq_source]
  change m.factorSylow 1 ⊓ m.image SymmetricFourWreath.A=_
  rw [A_eq_twoCore,m.image_twoCore]

theorem factors_centralize : m.factor 1≤centralizer (m.factor turn:Set G) := by
  intro x hx y hy
  obtain ⟨_,⟨a,rfl⟩,rfl⟩:=hx
  obtain ⟨_,⟨b,rfl⟩,rfl⟩:=hy
  rw [←map_mul,←map_mul]
  exact congrArg m.embedding (factor_commute turn_ne_one b a).eq

theorem terminalFour_centralizes_second_factor :
    m.terminalFour≤centralizer (m.factor turn:Set G) := by
  rw [m.terminalFour_eq_source]
  exact (inf_le_left.trans inf_le_right).trans m.factors_centralize

end CFSG.Quasithin.Chapter13.Section09.Marking
