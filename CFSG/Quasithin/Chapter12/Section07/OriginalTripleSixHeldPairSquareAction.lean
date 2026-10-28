module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPairJoin
public import Theory.GroupTheory.ExtraspecialSquareSixPlus

/-!
# The actual square action of the original extraspecial normalizer

Conjugation by the full normalizer acts on the square form of the same P.
An automorphism trivial on P/Z(P) is inner; the original self-centralizer
then makes the full kernel exactly P. All action formulas use the literal
normalizer conjugation and central quotient projection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem square_normalizer_kernel (P : Subgroup G) [IsExtraspecial 2 P]
    (hC : centralizer (P : Set G)≤P) :
    ((ExtraspecialSquare.isometryAction P).comp P.normalizerMonoidHom).ker=
      P.subgroupOf (normalizer (P : Set G)) := by
  apply le_antisymm
  · intro x hx
    have ha : P.normalizerMonoidHom x∈(quotientAut (center P)).ker :=
      (ExtraspecialSquare.isometryAction_eq_one_iff P _).mp hx
    obtain ⟨r,hr⟩ := (IsExtraspecial.quotientAut_center_ker_eq_range_conj (p:=2)).le ha
    have hc : (r:G)⁻¹*x.val∈centralizer (P : Set G) := by
      intro p hp
      have he := congrArg (fun f : MulAut P => (f (⟨p,hp⟩:P) : G)) hr
      change (r:G)*p*(r:G)⁻¹=x.val*p*x.val⁻¹ at he
      calc
        p*((r:G)⁻¹*x.val) = (r:G)⁻¹*((r:G)*p*(r:G)⁻¹)*x.val := by group
        _ = (r:G)⁻¹*(x.val*p*x.val⁻¹)*x.val := by rw [he]
        _ = ((r:G)⁻¹*x.val)*p := by group
    have hh := P.mul_mem r.property (hC hc)
    change x.val∈P
    simpa only [mul_inv_cancel_left] using hh
  · intro x hx
    apply (ExtraspecialSquare.isometryAction_eq_one_iff P _).mpr
    change P.normalizerMonoidHom x∈(quotientAut (center P)).ker
    rw [IsExtraspecial.quotientAut_center_ker_eq_range_conj (p:=2)]
    refine ⟨⟨x.val,hx⟩,?_⟩
    ext p
    rfl

omit [Finite G] in
private theorem elementary_square_displacement
    (P E : Subgroup G) [IsExtraspecial 2 P] [IsElementaryAbelian 2 E]
    (hPE : P≤normalizer (E : Set G))
    (u : normalizer (P : Set G)) (hu : u.val∈E) :
    ∀ v, ExtraspecialSquare.form P
      ((ExtraspecialSquare.isometryAction P (P.normalizerMonoidHom u)).val v-v)=0 := by
  apply ExtraspecialSquare.singular_displacement
  intro p
  apply Subtype.ext
  change (u.val*p.val*u.val⁻¹*p.val⁻¹)^2=1
  apply elemPow_eq_one_of_isElementaryAbelian (A:=E) _
  have hh := (hPE p.property u.val⁻¹).mp (E.inv_mem hu)
  simpa only [mul_assoc] using E.mul_mem hu hh

private theorem plus_normalizer_action (P : Subgroup G) [IsExtraspecial 2 P]
    (hP : Nat.card P=128) (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A=16) (hC : centralizer (P : Set G)≤P) :
    ∃ e : (ExtraspecialSquare.form P).IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)),
      ∃ f : normalizer (P : Set G)→*Equiv.Perm (Fin 8),
        f.ker=P.subgroupOf (normalizer (P : Set G)) ∧
        ∀ (y : normalizer (P : Set G)) (v : P⧸center P),
          (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val
            (e (Additive.ofMul v))=
              e (Additive.ofMul (quotientAut (center P) (P.normalizerMonoidHom y) v)) := by
  obtain ⟨e,b,hbk,hbe⟩ := ExtraspecialSquare.plus_six_automorphism_action P hP A hA
  let s := ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv
  let f := s.symm.toMonoidHom.comp (b.comp P.normalizerMonoidHom)
  have hf : f.ker=((ExtraspecialSquare.isometryAction P).comp P.normalizerMonoidHom).ker := by
    ext y
    change s.symm (b (P.normalizerMonoidHom y))=1 ↔
      ExtraspecialSquare.isometryAction P (P.normalizerMonoidHom y)=1
    rw [s.symm.map_eq_one_iff,ExtraspecialSquare.isometryAction_eq_one_iff]
    change P.normalizerMonoidHom y∈b.ker ↔ P.normalizerMonoidHom y∈(quotientAut (center P)).ker
    rw [hbk,IsExtraspecial.quotientAut_center_ker_eq_range_conj (p:=2)]
  refine ⟨e,f,hf.trans (square_normalizer_kernel P hC),?_⟩
  intro y v
  change (s (s.symm (b (P.normalizerMonoidHom y)))).val (e (Additive.ofMul v))=_
  rw [s.apply_symm_apply]
  exact hbe _ _

variable {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual full normalizer acts faithfully modulo the same P on eight
letters through its square form. Both original elementary planes have
singular displacement in this same action. -/
theorem original_tripleSix_escaping_pair_square_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      let Y := normalizer (P : Set G)
      P≤(T : Subgroup G) ∧ (T : Subgroup G)≤Y ∧ Nat.card P=128 ∧ ∃ hEx : IsExtraspecial 2 P, letI := hEx
      
      Nonempty (P≃*DihedralCentralProductThree.Model) ∧
      Nat.card (U⊓P : Subgroup G)=16 ∧ Nat.card ((U.subgroupOf T).map π)=4 ∧
      ∃ z : G, orderOf z=2 ∧ z∈U ∧
        centerIn P=zpowers z ∧ centerIn (T : Subgroup G)=zpowers z ∧
        centralizer (P : Set G)=zpowers z ∧ Y≤centralizer ({z} : Set G) ∧
        normalizer (K : Set G)⊓centralizer ({z} : Set G)≤Y ∧
        let H := centralizer ({(t:G)} : Set G)
        let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
        let B := conjugateSpanBy Lt H
        ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
          ∃ hWe : IsElementaryAbelian 2 W, letI := hWe
          let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
          let I := normalizer (W : Set G)
          U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ U⊔W=R ∧
          Nat.card W=64 ∧ (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧
          centralizer (W : Set G)=W ∧ I.pCoreIn 2=W ∧
          Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
          (U⊓P : Subgroup G)≠W⊓P ∧
          let Q := I⊓centralizer ({z} : Set G)
          Q≤Y ∧
            (∃ q : Q→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=P.subgroupOf Q) ∧
            let Q₀ := normalizer (K : Set G)⊓centralizer ({z} : Set G)
            (∃ q₀ : Q₀→*Equiv.Perm (Fin 4), Function.Surjective q₀ ∧ q₀.ker=P.subgroupOf Q₀) ∧
            Q₀≠Q ∧ Q₀⊓Q=(T : Subgroup G) ∧ Q₀.pCoreIn 2≠Q.pCoreIn 2 ∧
            let J := Q₀⊔Q
            J≤Y ∧ ChapterF.IsGoldschmidtTriple (Q₀.subgroupOf J) (Q.subgroupOf J) ∧
              (Q₀.subgroupOf J).pCoreIn 2≠(Q.subgroupOf J).pCoreIn 2 ∧ J.pCoreIn 2=P ∧
              ∃ e : (ExtraspecialSquare.form P).IsometryEquiv
                (ClassicalOrthogonal.formD 3 (ZMod 2)),
                ∃ f : Y→*Equiv.Perm (Fin 8), f.ker=P.subgroupOf Y ∧
                  (∀ (y : Y) (v : P⧸center P),
                    (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val
                      (e (Additive.ofMul v))=
                        e (Additive.ofMul (quotientAut (center P) (P.normalizerMonoidHom y) v))) ∧
                  ∀ y : Y, y.val∈U ∨ y.val∈W →
                    ∀ v, ClassicalOrthogonal.formD 3 (ZMod 2)
                      ((ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val v-v)=0 := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP⟩ :=
    original_tripleSix_escaping_pair_join h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Y := normalizer (P : Set G)
  let := hEx
  let := D.elementary
  let := hWe
  let A := (U⊓P).subgroupOf P
  let : IsElementaryAbelian 2 (U⊓P : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf inf_le_right
  have hA : Nat.card A=16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show U⊓P≤P from inf_le_right)).toEquiv).trans hUP
  have hC : centralizer (P : Set G)≤P :=
    hCP.le.trans (hZP.symm.le.trans inf_le_left)
  obtain ⟨e,f,hfk,hfe⟩ := plus_normalizer_action P hPc A hA hC
  have hTM : (T : Subgroup G)≤normalizer (K : Set G) := by
    rw [(original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.2.2]
    exact le_sup_right
  have hPU : P≤normalizer (U : Set G) := by
    rw [(original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.1]
    exact hPT.trans hTM
  have hPW : P≤normalizer (W : Set G) := hPT.trans (hTN.trans inf_le_right)
  have hsing (E : Subgroup G) [IsElementaryAbelian 2 E]
      (hPE : P≤normalizer (E : Set G)) (y : Y) (hy : y.val∈E) :
      ∀ v, ClassicalOrthogonal.formD 3 (ZMod 2)
        ((ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val v-v)=0 := by
    intro v
    obtain ⟨w,rfl⟩ := e.surjective v
    change ClassicalOrthogonal.formD 3 (ZMod 2)
      ((ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val
        (e (Additive.ofMul w.toMul))-e (Additive.ofMul w.toMul))=0
    rw [hfe y w.toMul]
    have hm := e.toLinearEquiv.map_sub
      ((ExtraspecialSquare.isometryAction P (P.normalizerMonoidHom y)).val w) w
    have hh := congrArg (ClassicalOrthogonal.formD 3 (ZMod 2)) hm
    exact hh.symm.trans ((e.map_app _).trans
      (elementary_square_displacement P E hPE y hy w))
  refine ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,e,f,hfk,hfe,?_⟩
  intro y hy
  rcases hy with hy | hy
  · exact hsing U hPU y hy
  · exact hsing W hPW y hy

end CFSG.Quasithin.Chapter12.Section07
