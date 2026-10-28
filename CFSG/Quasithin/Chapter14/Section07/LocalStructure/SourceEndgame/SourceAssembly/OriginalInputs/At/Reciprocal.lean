module
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ReciprocalEven

/-!
# Reciprocal parity from structure at the original G,T

The first-neighborhood kernel centralizes the natural module V, hence lies
in O₂(LT) by the same-ambient natural-action theorem. The last edge of the
original critical path places its terminal image in an H-conjugate of Q.
The genuine relative Sylow input makes its S₅ image even, and the allowed
H-rechoice preserves the original U.

The last theorem applies this to the literal reciprocal quotient required
by 14.7.70. Structural1222At retains producer qt-d-1222-source; the earlier
image statements and final 14.7.75 assembly remain with qt-d-14775-source.
The universal public APIs and all original maps are preserved.
Source: AS F.9.13, Notation 14.7.1 and 14.7.66–70, pp.1043,1070–1075.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The first neighborhood detects the natural action on V. -/
theorem Data.base_kernel_le_Q_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (ballKernel (geometryFamily (L := L) F)
      (base (geometryFamily (L := L) F) false) 1).map (GeometryGroup T L F).subtype ≤ Q T L := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  intro x hx
  obtain ⟨x,hx,rfl⟩ := hx
  have hxM : (x:G) ∈ L ⊔ (T : Subgroup G) := by
    have hh := ballKernel_le_stabilizer Ω (base Ω false) 1 hx
    have hh' : x ∈ Ω false := by simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
    exact hh'
  change (x:G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2
  rw [← d.natural.centralizer_LT_at structural]
  refine ⟨hxM,?_⟩
  intro v hv
  by_cases h1 : v=1
  · simp [h1]
  have hzV : d.z ∈ V := F.le_seed 1 (d.point.symm ▸ mem_zpowers d.z)
  obtain ⟨l,hl,he⟩ := d.natural.vector_transitive hzV hv d.z_ne_one h1
  let l' : K := ⟨l,(le_sup_left : L ≤ L ⊔ (T:Subgroup G)).trans le_sup_left hl⟩
  have hlfix : l' • base Ω false = base Ω false := by
    apply MulAction.mem_stabilizer_iff.mp
    have hh : l' ∈ Ω false := mem_sup_left hl
    simpa only [Subgroup.CosetGeometry.stabilizer_base] using hh
  have hneigh : (graph Ω).Adj (base Ω false) (l' • base Ω true) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso Ω l').toHom.map_adj
      (show (graph Ω).Adj (base Ω false) (base Ω true) from
        ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base Ω false true⟩)
    change (graph Ω).Adj (l' • base Ω false) (l' • base Ω true) at hh
    simpa only [hlfix] using hh
  have hefix := hx (l' • base Ω true) ((mem_ball_one Ω _ _).mpr (Or.inl hneigh))
  have hm : l'⁻¹*x*l' ∈ Ω true := by
    have hh : l'⁻¹*x*l' ∈ stabilizer Ω (base Ω true) := by
      change (l'⁻¹*x*l') • base Ω true = base Ω true
      rw [mul_smul,mul_smul,hefix,inv_smul_smul]
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hc : l⁻¹*(x:G)*l ∈ centralizer ({d.z} : Set G) := by
    rw [←d.centralizer_eq]
    exact hm
  have hz := mem_centralizer_singleton_iff.mp hc
  have hh := congrArg (fun y : G => l*y*l⁻¹) hz
  have hv' : l*d.z*l⁻¹ = v := he
  have heq : (x:G)*(l*d.z*l⁻¹)=(l*d.z*l⁻¹)*(x:G) := by
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_inv_cancel,mul_one] using hh
  rw [hv'] at heq
  exact heq.symm


/-- The last edge transports the original Q image to the terminal vertex. -/
theorem Data.source_terminal_even_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages) (x : G) (hx : x ∈ F.U) :
    ∃ y : F.H, (y:G)=(c.gammaConjugator:G)*x*(c.gammaConjugator:G)⁻¹ ∧
      d.qH y ∈ alternatingGroup (Fin 5) := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let w := c.path.getVert (c.b-1)
  let t := c.gammaConjugator⁻¹ • base Ω true
  have hb := c.three_le
  have hedge : (graph Ω).Adj w t := by
    have hh := c.path.adj_getVert_succ (i:=c.b-1) (by rw [c.length]; omega)
    have he : c.b-1+1=c.b := by omega
    rw [he] at hh
    have hend : c.path.getVert c.b = t := by
      rw [←c.length,SimpleGraph.Walk.getVert_length]
    rw [hend] at hh
    exact hh
  have hwt : w.type=false := by
    have hh := hedge.1
    change w.type ≠ true at hh
    cases he : w.type <;> simp_all
  obtain ⟨g,hgw,hgt⟩ := incident_common_translate Ω hedge.2
  rw [hwt] at hgw
  change g • base Ω true = c.gammaConjugator⁻¹ • base Ω true at hgt
  have ha : c.gammaConjugator*g ∈ Ω true := by
    have hh : c.gammaConjugator*g ∈ stabilizer Ω (base Ω true) := by
      change (c.gammaConjugator*g) • base Ω true = base Ω true
      rw [mul_smul,hgt,smul_inv_smul]
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
  obtain ⟨x',hx',he⟩ := d.span_le_penultimate_kernel c hx
  have hk : g⁻¹*x'*g ∈ ballKernel Ω (base Ω false) 1 := by
    have hh := (conj_mem_ballKernel_iff Ω g⁻¹ x' w 1).mpr hx'
    rw [←hgw,inv_smul_smul] at hh
    simpa only [inv_inv] using hh
  have hQ : (g:G)⁻¹*(x':G)*(g:G) ∈ Q T L :=
    d.base_kernel_le_Q_at structural ⟨g⁻¹*x'*g,hk,rfl⟩
  let a : F.H := ⟨(c.gammaConjugator:G)*(g:G),ha⟩
  let q : F.H := ⟨(g:G)⁻¹*(x':G)*(g:G),Q_le_H F hQ⟩
  refine ⟨a*q*a⁻¹,?_,?_⟩
  · change ((c.gammaConjugator:G)*(g:G))*((g:G)⁻¹*(x':G)*(g:G))*
      ((c.gammaConjugator:G)*(g:G))⁻¹ = (c.gammaConjugator:G)*x*(c.gammaConjugator:G)⁻¹
    rw [←he]
    group
    rfl
  · have hq : d.qH q ∈ alternatingGroup (Fin 5) :=
      d.Q_image_even c earlier (mem_map_of_mem d.qH hQ)
    rw [map_mul,map_mul,map_inv]
    exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ hq _


/-- The precise reciprocal S₅ parity needed by 14.7.70, with the original rechoice. -/
theorem Data.source_reciprocal_even_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages) :
    (F.U.subgroupOf (conjugate F.H c.conjugator)).map
      (Rechoice.LocalGeometry.Preparation.reciprocalQuotient d c) ≤ alternatingGroup (Fin 5) := by
  rintro y ⟨x,hx,rfl⟩
  have hx' : (c.rechoice:G)*(x:G)*(c.rechoice:G)⁻¹ ∈ F.U :=
    (mem_normalizer_iff.mp (d.conjugationSection.normalized c.rechoice.property) (x:G)).mp hx
  obtain ⟨y,hy,hye⟩ := d.source_terminal_even_at structural c earlier _ hx'
  have he : Rechoice.LocalGeometry.Preparation.conjugateBack F.H c.conjugator x = y := by
    apply Subtype.ext
    change c.conjugator*(x:G)*c.conjugator⁻¹ = (y:G)
    rw [hy]
    simp only [CriticalPath.conjugator,mul_inv_rev,mul_assoc]
  change d.qH (Rechoice.LocalGeometry.Preparation.conjugateBack F.H c.conjugator x) ∈ _
  rw [he]
  exact hye

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
