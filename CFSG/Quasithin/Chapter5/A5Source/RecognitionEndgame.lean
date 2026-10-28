module
public import CFSG.Quasithin.Chapter5.A5Source.Crossing
public import CFSG.Quasithin.Chapter5.A5Source.DihedralEndgame
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FiveDihedralRecognition
public import Theory.Representation.BinaryPermutation.FivePairFaithful
/-!
The literal Chapter5 endgame from the original elementary conjugate cores.
The actual five-point action gives the core kernel, and commuting core
factors give centrality of C_S(L). Intrinsic five-core recognition constructs
the two dihedral factors, which the checked odd-residual argument controls.
Source5.1.7(1), printed633–634.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem baumann_normalizer_of_generated_elementary_cores
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hQ : IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2))
    (g : G) (hg : g ∈ normalizer (baumann (T : Subgroup G) : Set G))
    (hcross : baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom)
    (hgen : (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ⊔
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom =
        baumann (T : Subgroup G))
    : False := by
  have hdis := baumann_core_disjoint_of_escape d hout
  have hker := baumann_core_centralizer_of_escape d hout
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let C := S ⊓ centralizer (L : Set G)
  let W := Q.map (MulAut.conj g⁻¹).toMonoidHom
  change Q = S ⊓ centralizer (V : Set G) at hker
  let := hQ
  have hQC : Q = V ⊔ C := baumann_core_product_of_escape d hout
  have hQS : Q ≤ S := baumann_core_le_of_escape d hout
  have hVS : V ≤ S := (le_sup_left.trans hQC.ge).trans hQS
  have hCQ : C ≤ Q := le_sup_right.trans hQC.ge
  have hWS : W ≤ S := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hQS
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp ((normalizer (S:Set G)).inv_mem hg))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (W.subgroupOf S) := IsElementaryAbelian.subgroupOf hWS
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCQ
  let : IsElementaryAbelian 2 (C.subgroupOf S) := IsElementaryAbelian.subgroupOf inf_le_left
  have hCZ : C.subgroupOf S ≤ center S := by
    intro c hc
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    have hQcomm : Q ≤ centralizer ({(c:G)} : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : Q) ⟨c,hCQ hc⟩))
    have hWcomm : W ≤ centralizer ({(c:G)} : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : W) ⟨c,hcross hc⟩))
    exact mem_centralizer_singleton_iff.mp ((sup_le hQcomm hWcomm) (hgen.symm ▸ s.property))
  have hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) :=
    fun hh => hout (baumann_normalizer_of_thompson_centralizes d hh)
  obtain ⟨q,m,hq,hm,hr,he,himage⟩ := exists_baumann_action_marking d hJ
  have hSN : S ≤ normalizer (V : Set G) := inf_le_left.trans d.flag.T_normalizes
  let p := q.comp (inclusion hSN)
  have hp : p.range = Offenders.D 5 := by
    rw [←himage]
    ext x
    constructor
    · rintro ⟨s,rfl⟩; exact ⟨inclusion hSN s,s.property,rfl⟩
    · rintro ⟨s,hs,rfl⟩; exact ⟨⟨s,hs⟩,rfl⟩
  have hpk : p.ker = (V.subgroupOf S) ⊔ (C.subgroupOf S) := by
    have hkerS : p.ker = (S ⊓ centralizer (V : Set G)).subgroupOf S := by
      ext s
      change p s = 1 ↔ (s:G) ∈ S ∧ (s:G) ∈ centralizer (V : Set G)
      constructor
      · intro hh
        refine ⟨s.property,?_⟩
        intro x hx
        obtain ⟨y,rfl⟩ := hr.symm ▸ hx
        have hv := he (inclusion hSN s) y.toAdd
        change _ = m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) y.toAdd)) at hv
        rw [hh,map_one] at hv
        exact (mul_inv_eq_iff_eq_mul.mp hv).symm
      · intro hh
        apply BinaryPermutation.FivePair.core_injective
        apply LinearMap.ext
        intro x
        apply Multiplicative.ofAdd.injective
        apply hm
        change m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) = m (Multiplicative.ofAdd x)
        have heq := he (inclusion hSN s) x
        change _ = m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) at heq
        rw [←heq]
        exact mul_inv_eq_iff_eq_mul.mpr (hh.2 _ (hr.le ⟨_,rfl⟩)).symm
    calc
      p.ker = (S ⊓ centralizer (V : Set G)).subgroupOf S := hkerS
      _ = Q.subgroupOf S := congrArg (fun H : Subgroup G => H.subgroupOf S) hker.symm
      _ = (V ⊔ C).subgroupOf S := congrArg (fun H : Subgroup G => H.subgroupOf S) hQC
      _ = V.subgroupOf S ⊔ C.subgroupOf S := subgroupOf_sup hVS inf_le_left
  have hgen' : V.subgroupOf S ⊔ C.subgroupOf S ⊔ W.subgroupOf S = ⊤ := by
    rw [←subgroupOf_sup hVS inf_le_left,←hQC,←subgroupOf_sup hQS hWS]
    exact hgen ▸ subgroupOf_self S
  let m0 : Multiplicative (BinaryPermutation.core (Fin 5)) →* V.subgroupOf S := {
    toFun := fun x => ⟨⟨m x,hVS (hr.le ⟨x,rfl⟩)⟩,hr.le ⟨x,rfl⟩⟩
    map_one' := Subtype.ext (Subtype.ext (map_one m))
    map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul m x y)) }
  have hmi : Function.Injective m0 := fun x y hh => hm (congrArg (fun z : V.subgroupOf S => ((z:S):G)) hh)
  have hms : Function.Surjective m0 := by
    intro v
    obtain ⟨x,hx⟩ := hr.ge v.property
    exact ⟨x,Subtype.ext (Subtype.ext hx)⟩
  let f := MulEquiv.ofBijective m0 ⟨hmi,hms⟩
  have hfe : ∀ (s:S) (x : BinaryPermutation.core (Fin 5)),
      (f (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) : S) =
        s * (f (Multiplicative.ofAdd x) : S) * s⁻¹ := by
    intro s x
    apply Subtype.ext
    exact (he (inclusion hSN s) x).symm
  have hd : Disjoint (V.subgroupOf S) (C.subgroupOf S) := by
    rw [disjoint_def]
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp hdis hx hy)
  obtain ⟨e⟩ := Offenders.dihedral_square_of_core_action (V.subgroupOf S) (C.subgroupOf S)
    (W.subgroupOf S) hCZ hd p hp hpk hgen' f hfe
  exact hout (baumann_normalizer_of_dihedral_square d e)
end CFSG.Quasithin.Chapter5.A5Source
