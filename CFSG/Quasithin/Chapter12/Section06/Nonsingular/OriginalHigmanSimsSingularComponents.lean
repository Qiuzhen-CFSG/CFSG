module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularComponentsNative
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsCenter
public import Theory.GroupTheory.PResidual.CubicCoreQuotient
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# The alternating-five quotient of the actual common HS residual

Restrict the original central quotient of Kᵥ to its actual centralizer of
z. Its full covering kernel is a two-group, and its image is the native
two-central involution centralizer. Removing the intrinsic two-cores
therefore gives S₅. The prime-to-three residual has quotient A₅, and is
two-perfect; the quasisimple quotient criterion makes it perfect.

The original residual-intersection identity transports both assertions to
J = O^{3′}(Gᵥ ∩ G_z). This identifies the literal common subgroup. It does
not assert that J is subnormal, or a C-component, in the whole G_z.

Source: the common residual in the original HS inspection for
Aschbacher--Smith 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem symmetricFive_primeToResidual :
    primeToResidual 3 (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  apply primeToResidual_eq_of_generated (alternatingGroup (Fin 5))
    (by rw [alternatingGroup.index_eq_two]; decide)
    _ Equiv.Perm.closure_three_cycles_eq_alternating
  intro x hx
  refine ⟨1,?_⟩
  simpa only [pow_one,hx.orderOf] using pow_orderOf_eq_one x

private theorem residual_of_symmetricFive_core_quotient
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 5)) :
    Group.IsPerfect (primeToResidual 3 A) ∧
      Nonempty ((primeToResidual 3 A ⧸ pCore 2 (primeToResidual 3 A)) ≃*
        alternatingGroup (Fin 5)) := by
  let d := (primeToResidualCoreQuotientImage (A := A) 3 2).trans
    ((primeToResidualEquiv 3 e).trans (MulEquiv.subgroupCongr symmetricFive_primeToResidual))
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (primeToResidual 3 A ⧸ pCore 2 (primeToResidual 3 A)) :=
    IsQuasisimple.of_mulEquiv d.symm
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (primeToResidual 3 A)) pCore_isPGroup
      (isPPerfect_primeToResidual (G := A) 3 2 (by decide))
  exact ⟨Group.IsPerfect.top_iff.mp ht.perfect,⟨d⟩⟩

/-- The common residual is perfect and its actual two-core quotient is A₅.
The full covering kernel is retained before restricting the original map. -/
theorem SourceHypothesis.nonsingular_hs_common_residual_perfect_quotient
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : G) (hz : z ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hz2 : z ^ 2 = 1) (hznot : z ∉ centralizer (Kv (v : G) : Set G)) :
    let B := Gv (v : G) ⊓ Gv z
    let J := (primeToResidual 3 B).map B.subtype
    Group.IsPerfect J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  let C := Kv (v : G)
  let A := (Gv z).subgroupOf C
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  obtain ⟨j,hj,hjc,_,_,himage,_,_,_,_,_,_⟩ :=
    H.nonsingular_hs_selected_centralizer_image D v hv hK e S z hz hz2 hznot
  let B := centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)
  change A.map q = B at himage
  let f : A →* B := (MulEquiv.subgroupCongr himage).toMonoidHom.comp (q.subgroupMap A)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr himage).surjective.comp (q.subgroupMap_surjective A)
  have hqk : q.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 f.ker := by
    have hfk : f.ker = (center C).comap A.subtype := by
      ext x
      change (⟨q x.val,?_⟩ : B) = 1 ↔ x.val ∈ center C
      rw [Subtype.ext_iff]
      exact show q x.val = 1 ↔ x.val ∈ center C from by rw [←hqk]; rfl
    rw [hfk]
    apply IsPGroup.comap_subtype
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [H.nonsingular_hs_ru_center_card D v hv hK (.inl ⟨e⟩)]
    decide
  obtain ⟨d⟩ := OriginalHigmanSimsSingularComponents.twoCentral_core_quotient_symmetricFive j hj hjc
  obtain ⟨hp,⟨dR⟩⟩ := residual_of_symmetricFive_core_quotient ((f.pCoreQuotientEquiv hf hk).trans d)
  let R := primeToResidual 3 A
  let J := (primeToResidual 3 (Gv (v : G) ⊓ Gv z : Subgroup G)).map
    (Gv (v : G) ⊓ Gv z).subtype
  let i := C.subtype.comp A.subtype
  have hi : Function.Injective i := C.subtype_injective.comp A.subtype_injective
  have he : R.map i = J := by
    rw [show R.map i = (R.map A.subtype).map C.subtype from (map_map _ _ _).symm,
      map_embedded_primeToResidual_of_hom,subgroupOf_map_subtype,inf_comm (Gv z) C]
    exact H.nonsingular_hs_intersection_primeToResidual D v hv hK e (Gv z)
  let r := (R.equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr he)
  let : Group.IsPerfect R := hp
  exact ⟨Group.IsPerfect.ofSurjective (f := r.toMonoidHom) r.surjective,
    ⟨(QuotientGroup.congr _ _ r.symm (pCore_map_iso 2 r.symm)).trans dR⟩⟩

end CFSG.Quasithin.Chapter12.Section06
