module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicGeneratingShifts

/-!
# Controlled large-image shifts in the remaining cubic branches

The three pair swaps together with the even involution (12)(34)
generate S₆: the original swaps and their conjugates contain a connected
chain on all six letters. Even involution fusion supplies a conjugate plane
generating with any prescribed even involution. The original plane or
Borel radical contains that plane image. The no-supplement theorem lifts
this generation across the full cubic kernel E, retaining E/Q.

Apply this to the controlled even subactor of the same large critical
path. The selected edge generates the original local stabilizer with that
subactor. Transporting a strict Baumann slice to this edge forces the
backward critical path, with one conjugator fixing the source vertex and
all overlap vertices identified. The whole-core and literal C.1.32
applications preserve both full moving covers and the original radical.

The paired small-image selectors are in CubicPlaneSelectors. Strict-slice
existence, the remaining compatible small-image path choices, R4/R6
comparisons and the terminal contradictions still have to be proved;
these shift theorems do not assert core exhaustion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)--(5.8), printed pp.917--920, and (5.11)--(5.12), pp.923--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk


namespace PlaneSelection
private def evenChain : S := Equiv.ofBijective
  (fun i : Fin 6 => (![2,3,5,4,1,0] : Fin 6 → Fin 6) i) (by decide)
private theorem even_actor_generates : D ⊔ zpowers position.val = ⊤ := by
  let H := D ⊔ zpowers position.val
  apply chain_generates H evenChain
  have cert : ∀ i : Fin 5, ∃ j : Fin 3,
      roots j = Equiv.swap (evenChain i.castSucc) (evenChain i.succ) ∨
      position.val*roots j*position.val⁻¹ =
        Equiv.swap (evenChain i.castSucc) (evenChain i.succ) := by decide
  intro i
  obtain ⟨j,hj | hj⟩ := cert i
  · rw [←hj]
    exact mem_sup_left (roots_mem j)
  · rw [←hj]
    exact H.mul_mem (H.mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (roots_mem j)))
      (H.inv_mem (mem_sup_right (mem_zpowers _)))

private theorem even_actor_conjugate (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) :
    ∃ g : alternatingGroup (Fin 6),
      D.map (MulAut.conj g.val).toMonoidHom ⊔ zpowers a.val = ⊤ := by
  have hp : orderOf position = 2 := orderOf_eq_prime (by decide) (by decide)
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj position a hp ha)
  have he : (MulAut.conj g.val).toMonoidHom position.val = a.val := congrArg Subtype.val hg
  refine ⟨g,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj g.val).toMonoidHom) even_actor_generates
  simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,he,
    map_top_of_surjective (MulAut.conj g.val).toMonoidHom (MulAut.conj g.val).surjective] using hh

private theorem even_actor_choices (u : S) (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) :
    ∃ g : alternatingGroup (Fin 6),
      (D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj g.val).toMonoidHom ⊔
        zpowers a.val = ⊤ := by
  let c : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal u⁻¹
  let b : alternatingGroup (Fin 6) := c a
  have hb : orderOf b = 2 := (c.orderOf_eq a).trans ha
  obtain ⟨k,hk⟩ := even_actor_conjugate b hb
  let g : alternatingGroup (Fin 6) := MulAut.conjNormal u k
  refine ⟨g,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hk
  have hback : (MulAut.conj u).toMonoidHom b.val = a.val := by
    change u*(u⁻¹*a.val*u)*u⁻¹=a.val
    group
  have hcomp : (MulAut.conj g.val).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.conj k.val).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change (u*k.val*u⁻¹)*(u*x*u⁻¹)*(u*k.val*u⁻¹)⁻¹=u*(k.val*x*k.val⁻¹)*u⁻¹
    group
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,hback,
    map_top_of_surjective (MulAut.conj u).toMonoidHom (MulAut.conj u).surjective,map_map] at hh
  rw [map_map,hcomp]
  exact hh
end PlaneSelection

include h e hz hk in
private theorem remaining_even_actor_generating_neighbor
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (A.comap (embedM Rg)).map π)
    (ha2 : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ Q Rg t ⊔ A = stabilizer Rg (alpha Rg) := by
  let := h.relative_normal
  let A₀ := A.comap (embedM Rg)
  have hmapA : A₀.map (embedM Rg) = A := map_comap_eq_self
    (hAG.trans_eq (stabilizer_m_base Rg))
  obtain ⟨k,hkgen⟩ := PlaneSelection.even_actor_choices
    u ⟨a,haeven⟩ (by simpa only [Subgroup.orderOf_mk] using ha2)
  have hkL : k.val ∈ (L.subgroupOf (L ⊔ R)).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  have hm : ((Rg).map (MulAut.conj g).toMonoidHom).map π =
      ((Rg).map π).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change π (g*x*g⁻¹) = k.val*π x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let F := (Rg).map (MulAut.conj g).toMonoidHom ⊔ A₀
  have hQF : pCore 2 M ≤ F := by
    rw [←hQ]
    exact (map_mono h.relative_radical.twoCore_le).trans le_sup_left
  have hD : D.map (MulAut.conj u).toMonoidHom ≤ (Rg).map π := by
    rcases hR with hp | hb
    · exact hp.ge
    · rw [hb]
      exact map_mono BorelCalculation.plane_le_borel
  have hfullF : F.map π = ⊤ := by
    rw [Subgroup.map_sup,hm]
    apply top_unique
    rw [←hkgen]
    exact sup_le_sup (map_mono hD) (zpowers_le.mpr ha)
  have hFE : F ⊔ extensionKernel h = ⊤ := by
    have he := congrArg (Subgroup.comap π) hfullF
    rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
  have hEF : extensionKernel h ≤ F := by
    have he := extensionKernel_no_supplement h F (hFE ▸ le_top)
    rw [extensionKernel_twoCore h,sup_of_le_left hQF] at he
    exact he
  have hgen : (Rg).map (MulAut.conj g).toMonoidHom ⊔ A₀ = ⊤ := by
    change F = ⊤
    rwa [sup_of_le_left hEF] at hFE
  let f := (embedM Rg g)⁻¹
  have hf : f ∈ stabilizer Rg (alpha Rg) := by
    change f ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act Rg f (alpha Rg) = alpha Rg := hf
  refine ⟨act Rg f (beta Rg),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr
      (base_adjacent Rg)
  · have hh := congrArg (Subgroup.map (embedM Rg)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    have hmapR : ((Rg).map (embedM Rg)).map (MulAut.conj f⁻¹).toMonoidHom =
        ((Rg).map (MulAut.conj g).toMonoidHom).map (embedM Rg) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM Rg x*(f⁻¹)⁻¹=embedM Rg (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

include h e hz hk in
/-- A large critical image supplies its actual controlled even subactor
and an incident edge generating with that same subactor. -/
theorem large_remaining_generating_actor
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) :
    ∃ A : Subgroup (FreeAmalgam Rg), A ≤ U Rg a' ∧ IsPGroup 2 A ∧
      (¬ A ≤ Q Rg (alpha Rg)) ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z Rg (alpha Rg) ∧
      ∃ t, Adjacent Rg (alpha Rg) t ∧ Q Rg t ⊔ A = stabilizer Rg (alpha Rg) := by
  obtain ⟨A,hAU,hdisp,a,ha,ha2,heven⟩ := critical_radius_even_actor h e hz hk p hlarge
  have hAG : A ≤ stabilizer Rg (alpha Rg) :=
    (hAU.trans (DistanceEight.U_le_Z Rg a')).trans
      (critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) p.critical)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  have htwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg a')).to_le
    (hAU.trans (DistanceEight.U_le_Z Rg a'))
  have hAn : ¬ A ≤ Q Rg (alpha Rg) := by
    intro hn
    have hcom : A.comap (embedM Rg) ≤ pCore 2 M := by
      have hh := comap_mono (f := embedM Rg) hn
      rwa [Q_alpha_comap Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
    have hm : (A.comap (embedM Rg)).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [CubicAction.projection_kernel h e hz hk]
      exact hcom.trans le_sup_right
    have ha1 : a = 1 := mem_bot.mp (hm ▸ ha)
    rw [ha1,orderOf_one] at ha2
    contradiction
  exact ⟨A,hAU,htwo,hAn,hdisp,
    remaining_even_actor_generating_neighbor h e hz hk u hR A hAG a ha ha2 heven⟩

include h e hz hk in
/-- The large-image backward step uses an edge generating with its
controlled subactor. Every overlap uses the same actual conjugator. -/
theorem large_remaining_backward_shift_of_two_lt_slice
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)))
    (hdelta : Adjacent Rg delta (p.walk.getVert 1))
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
      act Rg g (p.walk.getVert 1) = t ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (act Rg g delta)) := by
  obtain ⟨A,hAU,htwo,hAn,hdisp,t,hat,hgen⟩ :=
    large_remaining_generating_actor h e hz hk u hR p hlarge
  have hAZ : A ≤ Z Rg a' := hAU.trans (DistanceEight.U_le_Z Rg a')
  have hZG : Z Rg a' ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) ha1 hat
  let c := act Rg g delta
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hindexc : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    exact controlled_actor_backward_not_le h e hz hb p A (hAZ.trans hZG) htwo hAn hdisp hat hct hgen hindexc
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨t,hat,?_,g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,hindexc⟩
  exact le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
    (hgen.symm.le.trans (sup_le_sup_left hAZ _))

omit hk in
include h e hz in
/-- Whole-core assembly supplies the controlled backward shift at every strict
slice of a large critical path in either remaining image branch. -/
theorem coreExhaustion_or_cubic_remaining_shifts :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ a' (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) →
          ∀ delta, Adjacent Rg delta (p.walk.getVert 1) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
            ∃ t, Adjacent Rg (alpha Rg) t ∧
              Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
              ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g delta)) := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hR⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,hR,fun a' p hlarge delta hdelta hindex =>
      large_remaining_backward_shift_of_two_lt_slice h e hz hk hb u hR p hlarge hdelta hindex⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application retains the same critical path, conjugator and
all overlap vertices in the large-image backward shift. -/
theorem rankTwo_or_cubic_remaining_shifts :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ a' (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) →
          ∀ delta, Adjacent Rg delta (p.walk.getVert 1) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
            ∃ t, Adjacent Rg (alpha Rg) t ∧
              Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
              ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g delta)) :=
  (coreExhaustion_or_cubic_remaining_shifts h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
