module
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.SourceCoordinates
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The original terminal centralizer and its Sylow product

The actual E×T₂ inside J(T) is a Sylow subgroup of C_G(E), because J(T)
is Sylow in C_G(t) and normalizes E. Central transfer gives E∩O²(C_G(E))=1.
The first original A4 residual already lies in this terminal group. The final
Sylow restriction retains the source's second-factor inclusion as its genuine
remaining generation input, to be supplied by the 13.9.10 assembly.
Source: Aschbacher--Smith, proof of 13.9.1, printed pp.973--974.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath TerminalSubgroup
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

/-- Each original local factor has its literal residual isomorphic to A4. -/
def factorResidualEquiv (i:C2) : residual (m.factor i) ≃* alternatingGroup (Fin 4) :=
  ((pResidual 2 (m.factor i)).equivMapOfInjective (m.factor i).subtype
    (m.factor i).subtype_injective).symm |>.trans
    (((pResidual 2 (m.factor i)).equivMapOfInjective (m.factorEquiv i).toMonoidHom
      (m.factorEquiv i).injective).trans
      (MulEquiv.subgroupCongr ((map_pResidual 2 (m.factorEquiv i)).trans
        (Equiv.Perm.twoResidual_eq_alternating (Fin 4)))))

theorem first_factor_normalizes_terminal : m.factor 1≤normalizer (terminal m.terminalFour:Set G) :=
  normalizes_terminal_of_core _ _ m.terminalFour_eq_factorCore

theorem first_factor_centralizes_second_residual :
    m.factor 1≤centralizer (residual (m.factor turn):Set G) :=
  m.factors_centralize.trans (centralizer_le (residual_le _))

theorem second_residual_le_terminal : residual (m.factor turn)≤terminal m.terminalFour :=
  residual_le_terminal _ _ (le_centralizer_iff.mp m.terminalFour_centralizes_second_factor)

variable [Finite G]

theorem exists_terminalFour_centralizer_sylow :
    ∃ P : Sylow 2 (centralizer (m.terminalFour:Set G)),
      (P:Subgroup (centralizer (m.terminalFour:Set G))).map
        (centralizer (m.terminalFour:Set G)).subtype=m.terminalFour⊔m.factorSylow turn := by
  let H:=centralizer ({m.t}:Set G)
  let E:=m.terminalFour
  let C:=centralizer (E:Set G)
  have hCH : C≤H := centralizer_le (Set.singleton_subset_iff.mpr m.t_mem_terminalFour)
  have hEH : E≤H := (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans hCH
  have hCE : centralizer (E.subgroupOf H:Set H)=C.subgroupOf H := by
    ext x
    rw [mem_centralizer_iff]
    constructor
    · intro hx y hy
      exact congrArg Subtype.val (hx ⟨y,hEH hy⟩ hy)
    · intro hx y hy
      exact Subtype.ext (mem_centralizer_iff.mp hx (y:G) hy)
  obtain ⟨S,hS⟩:=m.thompson_sylow_t
  rw [m.elementary_thompson] at hS
  have hSN : (S:Subgroup H)≤normalizer (E.subgroupOf H:Set H) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    have hgJ : (g:G)∈m.dihedralBase := hS ▸ mem_map_of_mem H.subtype hg
    exact le_normalizer_iff.mp m.base_normalizes_terminalFour (g:G) hgJ (x:G) hx
  obtain ⟨Q,hQ⟩:=S.exists_centralizer_sylow_of_normalizes (E.subgroupOf H) hSN
  let e : centralizer (E.subgroupOf H:Set H) ≃* C :=
    (MulEquiv.subgroupCongr hCE).trans (subgroupOfEquivOfLe hCH)
  refine ⟨Q.mapSurjective (f:=e.toMonoidHom) e.surjective,?_⟩
  change ((Q:Subgroup (centralizer (E.subgroupOf H:Set H))).map e.toMonoidHom).map C.subtype=_
  calc
    _ = ((Q:Subgroup (centralizer (E.subgroupOf H:Set H))).map
        (centralizer (E.subgroupOf H:Set H)).subtype).map H.subtype := by
      rw [map_map,map_map]
      rfl
    _ = ((S:Subgroup H)⊓centralizer (E.subgroupOf H:Set H)).map H.subtype := by rw [hQ]
    _ = m.dihedralBase⊓C := by
      rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,hS,hCE,map_subgroupOf_eq_of_le hCH]
    _ = E⊔m.factorSylow turn := m.base_inf_centralizer_terminalFour


/-- Multiplication gives the actual Sylow product in C_G(E). -/
theorem exists_terminalFour_centralizer_sylow_product :
    ∃ (P : Sylow 2 (centralizer (m.terminalFour:Set G)))
      (e : m.terminalFour × m.factorSylow turn ≃* P),
      ∀ a b, (((e (a,b):P):centralizer (m.terminalFour:Set G)):G)=(a:G)*(b:G) := by
  obtain ⟨P,hP⟩:=m.exists_terminalFour_centralizer_sylow
  obtain ⟨f,hf⟩:=exists_mulEquiv_prod_sup_of_disjoint_of_commuting m.terminalFour (m.factorSylow turn)
    m.terminalFour_disjoint_second m.terminalFour_commutes_second
  let g : P ≃* ↥(m.terminalFour⊔m.factorSylow turn) :=
    ((P:Subgroup (centralizer (m.terminalFour:Set G))).equivMapOfInjective
      (centralizer (m.terminalFour:Set G)).subtype
      (centralizer (m.terminalFour:Set G)).subtype_injective).trans (MulEquiv.subgroupCongr hP)
  refine ⟨P,f.trans g.symm,?_⟩
  intro a b
  calc
    _ = (g (g.symm (f (a,b))):G) := rfl
    _ = (f (a,b):G) := congrArg Subtype.val (g.apply_symm_apply _)
    _ = (a:G)*(b:G) := hf a b

/-- Central transfer removes E from the literal terminal residual. -/
theorem terminalFour_disjoint_terminal : Disjoint m.terminalFour (terminal m.terminalFour) := by
  obtain ⟨P,e,he⟩:=m.exists_terminalFour_centralizer_sylow_product
  exact disjoint_terminal_of_sylow_product _ _ (IsElementaryAbelian.isPGroup 2 _) P e he

/-- Once the two original residual cores generate T₂ in H, its given embedding
is Sylow in H; no conjugation changes the marked factor. -/
theorem exists_terminal_sylow_of_second_le
    (hsecond : m.factorSylow turn≤terminal m.terminalFour) :
    ∃ P:Sylow 2 (terminal m.terminalFour),
      (P:Subgroup (terminal m.terminalFour)).map (terminal m.terminalFour).subtype=m.factorSylow turn := by
  obtain ⟨P,e,he⟩:=m.exists_terminalFour_centralizer_sylow_product
  exact exists_terminal_sylow_of_sylow_product _ _ (IsElementaryAbelian.isPGroup 2 _) P e he hsecond

end CFSG.Quasithin.Chapter13.Section09.Marking
