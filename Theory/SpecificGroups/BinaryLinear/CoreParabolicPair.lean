module
public import Theory.SpecificGroups.BinaryLinear.EndpointParabolic
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Generating parabolics above a binary linear two-core quotient

In dimensions four and five, the centralizer of the quotient Sylow center
and its endpoint parabolic generate the binary linear group. Their full
preimages generate through any two-core kernel, remain proper, and are
invariant under every automorphism preserving the original Sylow subgroup.
Characteristic two descends to these Sylow overgroups. The endpoint core
quotient is still S₃ × S₃, by the prime-core preimage theorem.

The interior image retains the given quotient marking. This is the
intrinsic lifting step in Aschbacher--Smith 15.1.22(3), printed pp.1099--1100;
placement in the original maximal two-local subgroups is separate.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

private theorem center_centralizer_invariant {X : Type*} [Group X]
    (U : Subgroup X) (a : MulAut X) (ha : U.map a.toMonoidHom = U) :
    (centralizer ((center U).map U.subtype : Set X)).map a.toMonoidHom =
      centralizer ((center U).map U.subtype : Set X) := by
  rw [← centerIn_eq_map_center, map_centralizer_equiv]
  change centralizer ((centerIn U).map a.toMonoidHom : Set X) = _
  rw [centerIn_map_equiv,ha]

private theorem center_centralizer_proper {n : ℕ} (hn : n = 4 ∨ n = 5)
    (U : Sylow 2 (LinearGroup n)) :
    centralizer ((center (U : Subgroup (LinearGroup n))).map
      (U : Subgroup (LinearGroup n)).subtype : Set (LinearGroup n)) ≠ ⊤ := by
  have aux {m : ℕ} (hm : 3 ≤ m) (U : Sylow 2 (LinearGroup (m+1))) :
      centralizer ((center (U : Subgroup (LinearGroup (m+1)))).map
        (U : Subgroup (LinearGroup (m+1))).subtype : Set (LinearGroup (m+1))) ≠ ⊤ := by
    obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer U
    have he := sylow_center_centralizer_eq_endCuts (by omega) U b hb
    have hne : cutStabilizer b {i | i.val = 0 ∨ i.val = m-1} ≠ ⊤ := by
      intro ht
      have hle : cutStabilizer b ∅ ≤ cutStabilizer b {i | i.val = 0 ∨ i.val = m-1} :=
        ht ▸ le_top
      have hh := (cutStabilizer_le_iff b _ _).mp hle
      exact hh (show (⟨0,by omega⟩ : Fin m) ∈ {i | i.val = 0 ∨ i.val = m-1} from Or.inl rfl)
    exact he ▸ hne
  rcases hn with rfl | rfl
  · exact aux (by decide) U
  · exact aux (by decide) U

private theorem map_comap_equivariant {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (a : MulAut X) (b : MulAut Y)
    (he : ∀ x, q (a x) = b (q x)) (P : Subgroup Y)
    (hP : P.map b.toMonoidHom = P) :
    (P.comap q).map a.toMonoidHom = P.comap q := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change q (a x) ∈ P
    rw [he]
    exact hP ▸ mem_map_of_mem b.toMonoidHom hx
  · intro x hx
    refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
    change q (a.symm x) ∈ P
    have hh : b (q (a.symm x)) ∈ P := by rw [←he,a.apply_symm_apply]; exact hx
    rw [←hP,mem_map_equiv] at hh
    simpa only [b.symm_apply_apply] using hh

/-- The interior and endpoint parabolics lift through the original two-core.
They generate, remain proper, and are fixed by every Sylow-preserving
automorphism. The endpoint retains its literal S₃ × S₃ core quotient. -/
theorem exists_core_parabolic_pair {X : Type*} [Group X] [Finite X]
    (hf : generalizedFitting X = pCore 2 X)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : (X ⧸ pCore 2 X) ≃* SL(n,ZMod 2))
    (S : Sylow 2 X) :
    ∃ C E : Subgroup X, C ⊔ E = ⊤ ∧ C ≠ ⊤ ∧ E ≠ ⊤ ∧
      (S : Subgroup X) ≤ C ∧ (S : Subgroup X) ≤ E ∧
      generalizedFitting C = pCore 2 C ∧ generalizedFitting E = pCore 2 E ∧
      Nonempty ((E ⧸ pCore 2 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      (let q := (e.trans (slEquivLinear n)).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
       C.map q = centralizer (centerIn ((S : Subgroup X).map q) : Set (LinearGroup n))) ∧
      (∀ a : MulAut X, (S : Subgroup X).map a.toMonoidHom = S →
        C.map a.toMonoidHom = C ∧ E.map a.toMonoidHom = E) := by
  let t := e.trans (slEquivLinear n)
  let : Finite (LinearGroup n) := Finite.of_equiv (X ⧸ pCore 2 X) t.toEquiv
  let q := t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := t.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ t.injective,QuotientGroup.ker_mk']
  let U := S.mapSurjective (f := q) hq
  let B := centralizer ((center (U : Subgroup (LinearGroup n))).map
    (U : Subgroup (LinearGroup n)).subtype : Set (LinearGroup n))
  obtain ⟨P,hUP,hP,⟨ep⟩,hPinv,hgen⟩ := exists_endpoint_parabolic hn U
  let C := B.comap q
  let E := P.comap q
  have hUC : (U : Subgroup (LinearGroup n)) ≤ B := by
    intro x hx z hz
    obtain ⟨y,hy,rfl⟩ := hz
    exact congrArg Subtype.val ((mem_center_iff.mp hy) (⟨x,hx⟩ : U)).symm
  have hSC : (S : Subgroup X) ≤ C := (map_le_iff_le_comap).mp hUC
  have hSE : (S : Subgroup X) ≤ E := (map_le_iff_le_comap).mp hUP
  have hfit (D : Subgroup X) (hSD : (S : Subgroup X) ≤ D) :
      generalizedFitting D = pCore 2 D :=
    generalizedFitting_eq_pCore_of_normalized_by_pCore D hf
      ((pCore_isPGroup.le_sylow_of_normal S).trans (hSD.trans D.le_normalizer))
  have hEP : Nonempty ((E ⧸ pCore 2 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
    let f : E →* P := (q.comp E.subtype).codRestrict P (fun x => x.property)
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨x,hx⟩ := hq y
      exact ⟨⟨x,show q x ∈ P from hx.symm ▸ y.property⟩,Subtype.ext hx⟩
    have hfker : IsPGroup 2 f.ker := by
      have he : f.ker = q.ker.subgroupOf E := by ext x; change (⟨q x,x.property⟩ : P) = 1 ↔ q x = 1; exact Subtype.ext_iff
      rw [he,hk]
      exact pCore_isPGroup.comap_subtype
    exact ⟨(f.pCoreQuotientEquiv hfs hfker).trans ep⟩
  refine ⟨C,E,?_,?_,?_,hSC,hSE,hfit C hSC,hfit E hSE,hEP,?_,?_⟩
  · change B.comap q ⊔ P.comap q = ⊤
    rw [comap_sup_eq _ _ _ hq,show B ⊔ P = ⊤ from hgen,comap_top]
  · intro he
    exact center_centralizer_proper hn U ((comap_injective hq) (he.trans (comap_top q).symm))
  · intro he
    exact hP ((comap_injective hq) (he.trans (comap_top q).symm))
  · change (B.comap q).map q = centralizer (centerIn (U : Subgroup (LinearGroup n)) : Set _)
    rw [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top),centerIn_eq_map_center]
  · intro a ha
    let b := MulAut.congr t (quotientAut (pCore 2 X) a)
    have he (x : X) : q (a x) = b (q x) := by
      change t (QuotientGroup.mk' (pCore 2 X) (a x)) =
        t (quotientAut (pCore 2 X) a (t.symm (t (QuotientGroup.mk' (pCore 2 X) x))))
      rw [t.symm_apply_apply,quotientAut_apply_mk]
    have hUb : (U : Subgroup (LinearGroup n)).map b.toMonoidHom = U := by
      change ((S : Subgroup X).map q).map b.toMonoidHom = (S : Subgroup X).map q
      have hhom : b.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext (fun x => (he x).symm)
      rw [map_map,hhom,←map_map,ha]
    exact ⟨map_comap_equivariant q a b he B (center_centralizer_invariant _ b hUb),
      map_comap_equivariant q a b he P (hPinv b hUb)⟩

end BinaryLinear.InvariantNodeActions
