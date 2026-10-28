module
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.SourceGeneration
public import Theory.SpecificGroups.SymmetricFourResidualCore
/-!
# The actual A4 cores in the terminal residual

The original second S4 has the normal second-coordinate Klein four. Its core
is distinct from the split S4 core because the latter lies in B and the former
does not. Both cores are elementary of order four and internally fused in their
actual A4 residuals. The checked generation theorem therefore recognizes the
literal terminal residual and applies the source fixer obstruction. This leaf
retains only the concrete placement supplied by the marked normalizer split.
Source: Aschbacher--Smith, proof of 13.9.1, printed p.974.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath TerminalSubgroup
variable {G:Type*} [Group G] {d:Configuration G} (m:Marking d)

private theorem four_core_elementary (X:Subgroup G) (e:X≃*S4) :
    IsElementaryAbelian 2 (X.pCoreIn 2) := by
  have h0:IsElementaryAbelian 2 (pCore 2 X) := by
    let e0:(pCore 2 X)≃*Theory.SpecificGroups.SymmetricSix.DuadCalculation.core :=
      ((pCore 2 X).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr ((pCore_map_iso 2 e).trans
          Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq.symm))
    exact IsElementaryAbelian.of_surjective e0.symm.toMonoidHom e0.symm.surjective
  exact h0.map X.subtype

private theorem four_core_card (X:Subgroup G) (e:X≃*S4) : Nat.card (X.pCoreIn 2)=4 := by
  rw [pCoreIn,card_map_of_injective X.subtype_injective,
    Nat.card_congr ((pCore 2 X).equivMapOfInjective e.toMonoidHom e.injective).toEquiv,
    pCore_map_iso,←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]

private theorem four_core_le_residual (X:Subgroup G) (e:X≃*S4) : X.pCoreIn 2≤residual X :=
  map_mono (Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual_of_equiv e)

private theorem four_core_fusion (X H:Subgroup G) (e:X≃*S4) (hX:residual X≤H)
    (x y:G) (hx:x∈X.pCoreIn 2) (hy:y∈X.pCoreIn 2) (hnx:x≠1) (hny:y≠1) :
    IsConj (⟨x,hX (four_core_le_residual X e hx)⟩:H)
      ⟨y,hX (four_core_le_residual X e hy)⟩ := by
  obtain ⟨a,ha,rfl⟩:=hx
  obtain ⟨b,hb,rfl⟩:=hy
  have hcert:∀a:S4,a.sign=1→a^2=1→a≠1→
      ∀b:S4,b.sign=1→b^2=1→b≠1→
      ∃g:S4,g.sign=1∧g*a*g⁻¹=b := by decide +kernel
  have hea:e a∈Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
    rw [Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,←pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom ha
  have heb:e b∈Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
    rw [Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,←pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom hb
  obtain ⟨g,hg,hgab⟩:=hcert (e a) ((Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff _).mp hea).1 ((Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff _).mp hea).2 (by intro he;exact hnx (congrArg Subtype.val (e.injective (he.trans (map_one e).symm))))
    (e b) ((Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff _).mp heb).1 ((Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff _).mp heb).2 (by intro he;exact hny (congrArg Subtype.val (e.injective (he.trans (map_one e).symm))))
  have hgR:e.symm g∈pResidual 2 X := by
    have hm:e (e.symm g)∈(pResidual 2 X).map e.toMonoidHom := by
      rw [map_pResidual,Equiv.Perm.twoResidual_eq_alternating,MulEquiv.apply_symm_apply]
      exact hg
    exact (mem_map_iff_mem e.injective).mp hm
  have hgH:(e.symm g:G)∈H:=hX (mem_map_of_mem X.subtype hgR)
  apply isConj_iff.mpr
  refine ⟨⟨e.symm g,hgH⟩,Subtype.ext ?_⟩
  change (e.symm g:G)*(a:G)*(e.symm g:G)⁻¹=(b:G)
  have he:e.symm g*a*(e.symm g)⁻¹=b := by
    apply e.injective
    simpa only [map_mul,map_inv,MulEquiv.apply_symm_apply] using hgab
  exact congrArg Subtype.val he

private theorem second_axis_core (a:D8) : m.baseProductEmbedding (1,a)=
    m.embedding (SymmetricFourWreath.factor turn (square a)) := by
  apply congrArg m.embedding
  apply RegularWreathProduct.ext
  · funext i
    rcases c2_eq_one_or_turn i with rfl|rfl <;>
      simp [sylowEmbedding,pair,SymmetricFourWreath.factor,turn_ne_one,Ne.symm turn_ne_one]
  · rfl

private theorem second_plane_core : (m.factor turn).pCoreIn 2=
    ((⊥:Subgroup D8).prod (plane true)).map m.baseProductEmbedding := by
  let f:=m.embedding.comp (SymmetricFourWreath.factor turn)
  have hf:f.range=m.factor turn := by rw [MonoidHom.range_comp];rfl
  have hp:(plane true).map square=pCore 2 S4 := by
    rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
    ext x
    exact (by decide : ∀x:S4,(∃a:D8,a∈plane true ∧ square a=x) ↔
      x∈Theory.SpecificGroups.SymmetricSix.DuadCalculation.core) x
  rw [←hf,pCoreIn_range_of_injective 2 f (m.embedding_injective.comp (factor_injective turn)),←hp,map_map]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨(1,a),⟨by rfl,ha⟩,?_⟩
    exact m.second_axis_core a
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    change a=1 at ha
    subst a
    exact ⟨b,hb,(m.second_axis_core b).symm⟩

private theorem second_core_le_base : (m.factor turn).pCoreIn 2≤m.dihedralBase := by
  rw [m.second_plane_core,←m.range_baseProductEmbedding]
  exact map_le_range _ _

private theorem second_core_not_le_B : ¬(m.factor turn).pCoreIn 2≤m.B := by
  intro h
  have hm:m.baseProductEmbedding (1,DihedralGroup.sr 1)∈(m.factor turn).pCoreIn 2 := by
    rw [m.second_plane_core]
    exact mem_map_of_mem _ ⟨by rfl,by change _∈plane true;decide⟩
  have hh:=((m.elementaryGroup_coordinate 1 (DihedralGroup.sr 1) false false).mp (h hm)).2
  exact (by decide : DihedralGroup.sr (1:ZMod 4)∉plane false) hh

private theorem second_axis_core_center : m.baseProductEmbedding (1,DihedralGroup.r 2)=m.t*m.z := by
  rw [m.second_axis_core]
  have he:SymmetricFourWreath.factor turn (square (DihedralGroup.r 2))=SymmetricFourWreath.t*SymmetricFourWreath.z := by
    rw [SymmetricFourWreath.z,←mul_assoc,SymmetricFourWreath.t_sq,one_mul]
    simp only [SymmetricFourWreath.t,swap_factor,mul_one]
  rw [he,map_mul]
  rfl

private theorem second_center_mem_core : m.t*m.z∈(m.factor turn).pCoreIn 2 := by
  rw [←m.second_axis_core_center,m.second_plane_core]
  exact mem_map_of_mem _ ⟨by rfl,by change _∈plane true;decide⟩

variable [Finite G]

/-- The actual second S4 factor and the marked split S4 supply the two
four-cores of the terminal Sylow. Only their literal source placement remains
for the separately constructed marked centralizer splitting. -/
theorem terminal_psl3Two_of_marked_symmetric_core {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (X:Subgroup G) (eX:X≃*S4)
    (hX:residual X≤terminal m.terminalFour)
    (hVJ:X.pCoreIn 2≤m.dihedralBase) (hVB:X.pCoreIn 2≤m.B)
    (hz:m.t*m.z∈X.pCoreIn 2) :
    Nonempty (terminal m.terminalFour≃*Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      m.factor 1≤centralizer (terminal m.terminalFour:Set G) := by
  have hAH:(m.factor turn).pCoreIn 2≤terminal m.terminalFour :=
    (four_core_le_residual (m.factor turn) (m.factorEquiv turn)).trans m.second_residual_le_terminal
  have hBH:X.pCoreIn 2≤terminal m.terminalFour := (four_core_le_residual X eX).trans hX
  have hne:(m.factor turn).pCoreIn 2≠X.pCoreIn 2 := fun he=>m.second_core_not_le_B (he ▸ hVB)
  have hc:m.t*m.z≠1 := by
    rw [←m.second_axis_core_center]
    intro he
    have hh:=m.baseProductEmbedding_injective (he.trans (map_one m.baseProductEmbedding).symm)
    exact (by decide : ((1,DihedralGroup.r 2) : D8×D8)≠1) hh
  apply m.terminal_psl3Two_of_two_four_cores hG ((m.factor turn).pCoreIn 2) (X.pCoreIn 2)
    m.second_core_le_base hVJ hAH hBH
    (four_core_elementary _ (m.factorEquiv turn)) (four_core_elementary X eX)
    (four_core_card _ (m.factorEquiv turn)) (four_core_card X eX) hne m.second_center_mem_core hz
  · intro x hx ho
    exact four_core_fusion (m.factor turn) (terminal m.terminalFour) (m.factorEquiv turn)
      m.second_residual_le_terminal x (m.t*m.z) hx m.second_center_mem_core
      (by intro he;rw [he,orderOf_one] at ho;omega) hc
  · intro x hx ho
    exact four_core_fusion X (terminal m.terminalFour) eX hX x (m.t*m.z) hx hz
      (by intro he;rw [he,orderOf_one] at ho;omega) hc

end CFSG.Quasithin.Chapter13.Section09.Marking
