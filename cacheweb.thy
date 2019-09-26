

theory cache = Main:

datatype message = empty_message 
                   |  req_shared 
                    | req_exclusive
                    | invalidate 
		   | invalidate_ack | grant_shared | grant_exclusive

datatype cache_state = invalid| shared | exclusive

     

typedecl client 
  -- "an unspecified (arbitrary) type of locations 
      (adresses/names) for variables"
types 

  
  channel_state = "client \<Rightarrow> message"
 

record state=
    channel1:: channel_state

    channel2_4:: channel_state

    channel3:: channel_state

    home_sharer_list:: "client \<Rightarrow> bool"
    
    home_invalidate_list:: "client \<Rightarrow> bool"

    home_exclusive_granted:: bool

    home_current_command:: message

    home_current_client:: client

    cache:: "client \<Rightarrow> cache_state"



consts 
  client_set:: "client set"
constdefs
    state_permutating ::"state\<Rightarrow>state\<Rightarrow>(client\<Rightarrow>client)\<Rightarrow>client set\<Rightarrow> bool"
    "state_permutating s s' f cs == 
     home_exclusive_granted s' =home_exclusive_granted s  &

    home_current_command s' = home_current_command s  &

     (home_current_client s') = f (home_current_client s)&
    (ALL c:cs.(
    channel1 s' (f c)=channel1 s c  &

    channel2_4 s' (f c)= channel2_4 s c &

    channel3 s' (f c) =channel3 s c &

    home_sharer_list  s' (f c)=home_sharer_list s c &
    
    home_invalidate_list s' (f c)=home_invalidate_list s c &   

    cache s' (f c)=cache s c) )"

consts
  (*Init_state:: state*)
  c0::client
  cache0:: cache_state


constdefs  Init_state_spec::"state\<Rightarrow>client set\<Rightarrow>bool"
"Init_state_spec Init_state cs==
(ALL i:cs.(channel1 Init_state) i  = empty_message &
                  (channel2_4 Init_state) i = empty_message &
                  (channel3 Init_state) i = empty_message&
                  (cache  Init_state) i =  invalid&
                  (~ (home_sharer_list Init_state) i)&
                  (~(home_invalidate_list Init_state) i))&
( home_current_command Init_state) = empty_message&
(EX c0:cs.( home_current_client Init_state) = c0)&
~( home_exclusive_granted Init_state)"

constdefs
client_requests_shared_access_guard::"state\<Rightarrow>client\<Rightarrow>bool" 
 "client_requests_shared_access_guard s c ==
   (cache s) c = invalid & (channel1 s) c = empty_message"

constdefs
client_requests_exclusive_guard::"state\<Rightarrow>client\<Rightarrow>bool" 
 "client_requests_exclusive_guard s c ==
   ((cache s) c = invalid | (cache s) c = shared) & (channel1 s) c = empty_message"

constdefs
home_picks_new_request_guard::"state\<Rightarrow>client\<Rightarrow>bool"
"home_picks_new_request_guard s c ==(home_current_command s )=empty_message & ~(channel1 s) c = empty_message"

constdefs
home_picks_new_request_update::"state\<Rightarrow> state \<Rightarrow>client\<Rightarrow> bool"   
"home_picks_new_request_update s s' c == 
         s' = s
         \<lparr>channel1 := (channel1 ( s))(c := empty_message),
          home_current_client := c,
          home_current_command := (channel1 s c),
          home_invalidate_list := home_sharer_list (s)\<rparr>
"
(*(home_current_command s' )= (channel1 s) c&
                                         (channel1 s') = (channel1  s)( c:=empty_message)&
                                         ( ALL i:client_set.
                                           home_invalidate_list s' i =  home_sharer_list s i)&
                                          channel2_4 s'= channel2_4 s&
                                          channel3 s'= channel3 s&
                                          home_sharer_list s'=home_sharer_list s&                                                                     home_exclusive_granted s'= home_exclusive_granted s&   
                                          home_current_client s'= c&
                                          cache s'=cache s" *)
constdefs
  state_sim_on ::"state\<Rightarrow>state\<Rightarrow>client set\<Rightarrow>bool"
  " state_sim_on s s' cs==
  (ALL c:cs.(
                                              channel1 (s) ( c)=channel1 (s') c  &
                                              channel2_4 (s)  ( c)= channel2_4 (s') c &

                                              channel3 (s) (c) =channel3 (s') c &

                                               home_sharer_list (s)  (c)=home_sharer_list (s') c &
    
                                            home_invalidate_list (s)  (c)=home_invalidate_list (s') c &
                                                
                                                cache (s) ( c)=cache (s') c 
                                 ))"

(*constdefs
home_picks_new_request_update_abs::"state\<Rightarrow> state \<Rightarrow>client\<Rightarrow>client set\<Rightarrow> bool"   
"home_picks_new_request_update_abs s s' c cs== 
           
           (ALL c:cs.(
                      channel1 (s) ( c)=channel1 (s') c  &
                      channel2_4 (s)  ( c)= channel2_4 (s') c &
                      channel3 (s) (c) =channel3 (s') c &

                      home_sharer_list (s)  (c)=home_sharer_list (s') c &  
                                                          
                      cache (s) ( c)=cache (s') c 
                                 ))&
           home_invalidate_list s'=home_sharer_list s&
           channel1 s' =(channel1 ( s))(c := empty_message) &                  
           (home_current_command s' =req_shared | 
            home_current_command s'=req_exclusive)&
          (if  (ALL i:cs. ~(channel2_4 s i=grant_exclusive |cache s i=exclusive))
          then  ( home_exclusive_granted s' =True | 
                 home_exclusive_granted s'   =False)
          else home_exclusive_granted s'   =home_exclusive_granted s)
"*)

constdefs
home_picks_new_request_update_abs::"state\<Rightarrow> state \<Rightarrow>client\<Rightarrow> bool"   
"home_picks_new_request_update_abs s s' c == 
       s' = s
         \<lparr>
          home_current_client := c,
          home_current_command :=req_shared ,
          home_invalidate_list := home_sharer_list (s)\<rparr>|
        s' = s
         \<lparr>
          home_current_client := c,
          home_current_command :=req_exclusive ,
          home_invalidate_list := home_sharer_list (s)\<rparr>
"


constdefs
home_sends_invalidate_message_guard::"state\<Rightarrow>client\<Rightarrow> bool"   
"home_sends_invalidate_message_guard s  c == 
        ((home_current_command s )=req_shared & (home_exclusive_granted s) |
         (home_current_command s )=req_exclusive )&
          home_invalidate_list s c & channel2_4 s c = empty_message"

constdefs
sharer_invalidates_cache_guard::"state\<Rightarrow>client\<Rightarrow> bool" 
"sharer_invalidates_cache_guard s c ==
       channel2_4 s c = invalidate & channel3 s c  = empty_message"

constdefs
home_receives_invalidate_acknowledgement_guard ::"state\<Rightarrow>client\<Rightarrow> bool" 
     
"home_receives_invalidate_acknowledgement_guard s c==
      home_current_command s ~= empty_message & channel3 s c = invalidate_ack "


constdefs 
client_receives_shared_grant_guard :: "state \<Rightarrow>client \<Rightarrow>bool"
"client_receives_shared_grant_guard s c ==  channel2_4 s c = grant_shared "

constdefs
client_receives_exclusive_grant_guard:: "state \<Rightarrow>client \<Rightarrow>bool"
"client_receives_exclusive_grant_guard s c ==  channel2_4 s c = grant_exclusive "    

constdefs 
home_sends_reply_to_client_shared_guard ::" state \<Rightarrow> bool"
"home_sends_reply_to_client_shared_guard s ==
 home_current_command s = req_shared
      & ~home_exclusive_granted s & channel2_4 s (home_current_client s ) = empty_message"

constdefs
 home_sends_reply_to_client_exclusive_guard ::" state \<Rightarrow>client set\<Rightarrow> bool"
 "home_sends_reply_to_client_exclusive_guard s cs ==
  home_current_command s = req_exclusive
    & (ALL i: cs. ~ (home_sharer_list s) i)
    &  channel2_4 s (home_current_client s ) = empty_message"

constdefs 
   client_requests_shared_access_update :: " state \<Rightarrow> state \<Rightarrow> client\<Rightarrow>bool"
   " client_requests_shared_access_update s s' c == s' = s\<lparr>channel1:=(channel1 s)(c:=req_shared) \<rparr>"

constdefs 
   client_requests_exclusive_access_update :: " state \<Rightarrow> state \<Rightarrow> client\<Rightarrow>bool"
   " client_requests_exclusive_access_update s s' c == s' = s\<lparr>channel1:=(channel1 s)(c:=req_exclusive) \<rparr>"

constdefs 
   
  home_sends_invalidate_message_update :: " state \<Rightarrow> state \<Rightarrow> client\<Rightarrow>bool"
  " home_sends_invalidate_message_update s s' c == s' = s\<lparr> channel2_4:=(channel2_4 s) (c:= invalidate),
                   home_invalidate_list:= (home_invalidate_list(s))  (c:=False)  \<rparr>"

constdefs 
   home_receives_invalidate_acknowledgement_update ::" state \<Rightarrow> state \<Rightarrow> client\<Rightarrow>bool"
   " home_receives_invalidate_acknowledgement_update s s' c == s'=s\<lparr> channel3:=(channel3 (s)) (c:= empty_message),
                    home_sharer_list:= (home_sharer_list(s))  (c:=False),
                    home_exclusive_granted:=False \<rparr>"

constdefs 
    sharer_invalidates_cache_update ::" state \<Rightarrow> state \<Rightarrow> client\<Rightarrow>bool"
   "sharer_invalidates_cache_update s s' c == s'=s\<lparr> channel2_4:=(channel2_4 (s)) (c:= empty_message),
                        channel3:=(channel3 (s)) (c:= invalidate_ack),
                        cache:=(cache (s)) (c:= invalid)  \<rparr>"

constdefs 
    client_receives_shared_grant_update ::" state \<Rightarrow> state \<Rightarrow> client\<Rightarrow>bool"
   "client_receives_shared_grant_update s s' c == s'=s\<lparr> channel2_4:=(channel2_4 (s)) (c:= empty_message),                        
                        cache:=(cache (s)) (c:= shared)  \<rparr>"

constdefs 
    client_receives_exclusive_grant_update ::" state \<Rightarrow> state \<Rightarrow> client\<Rightarrow>bool"
   "client_receives_exclusive_grant_update s s' c == s'=s\<lparr> channel2_4:=(channel2_4 (s)) (c:= empty_message),                     
                        cache:=(cache (s)) (c:= exclusive)  \<rparr>"

constdefs 
    home_sends_reply_to_client_shared_update ::" state \<Rightarrow> state\<Rightarrow>bool"
   "home_sends_reply_to_client_shared_update s s'  == s'=s\<lparr>channel2_4:= (channel2_4 (s)) ((home_current_client (s)):= grant_shared),
                home_sharer_list:= (home_sharer_list (s))  ((home_current_client (s)):=True),
                 home_current_command:=empty_message  \<rparr>"

constdefs 
    home_sends_reply_to_client_exclusive_update ::" state \<Rightarrow> state \<Rightarrow>bool"
   "home_sends_reply_to_client_exclusive_update s s'  == s'=s\<lparr>channel2_4:= (channel2_4 (s)) ((home_current_client (s)):= grant_exclusive),
                home_sharer_list:= (home_sharer_list (s))  ((home_current_client (s)):=True),
                 home_current_command:=empty_message , home_exclusive_granted:=True \<rparr>"



consts traces:: "client set \<Rightarrow> (state list) set "
inductive "traces cs"
  intros
  Init_trace [intro]: "(Init_state_spec s cs) \<Longrightarrow> [s]: traces cs"
  client_requests_shared_access:
   "\<lbrakk>tr:traces cs; c:cs;
     client_requests_shared_access_guard (last tr) c;
     client_requests_shared_access_update (last tr) s c     \<rbrakk>\<Longrightarrow>
     tr@[s]:traces cs"

  client_requests_exclusive_access:"
   \<lbrakk> tr:traces cs; c:cs;
     client_requests_exclusive_guard (last tr) c;
     client_requests_exclusive_access_update (last tr) s c \<rbrakk>\<Longrightarrow>
     tr@[s]:traces cs"
      
  home_picks_new_request:
  "\<lbrakk>tr:traces cs; c:cs;
    home_picks_new_request_guard (last tr) c ;
    home_picks_new_request_update (last tr) s c
   \<rbrakk> \<Longrightarrow>  tr@[s]:traces cs"

  home_sends_invalidate_message:
  "\<lbrakk>tr:traces cs; c:cs;
   home_sends_invalidate_message_guard (last tr) c;
   home_sends_invalidate_message_update (last tr) s  c\<rbrakk>\<Longrightarrow>
   tr@[s]:traces cs"   
 
 home_receives_invalidate_acknowledgement:
  " \<lbrakk>tr:traces cs; c:cs;
     home_receives_invalidate_acknowledgement_guard  (last tr) c;
    home_receives_invalidate_acknowledgement_update (last tr) s c \<rbrakk>\<Longrightarrow> 
    tr@[s]:traces cs" 

 sharer_invalidates_cache:
 " \<lbrakk>tr:traces cs; c:cs; sharer_invalidates_cache_guard (last tr) c;
    sharer_invalidates_cache_update (last tr) s c\<rbrakk>\<Longrightarrow>
        tr@[s]:traces cs"

 client_receives_shared_grant:
 "\<lbrakk>tr:traces cs; c:cs; client_receives_shared_grant_guard (last tr) c;
   client_receives_shared_grant_update (last tr) s c \<rbrakk>\<Longrightarrow>
        tr@[s]:traces cs"
            
 client_receives_exclusive_grant:
  "\<lbrakk>tr:traces cs; c:cs; client_receives_exclusive_grant_guard (last tr) c  ;
     client_receives_exclusive_grant_update (last tr) s c\<rbrakk>\<Longrightarrow>
     tr@[s]:traces cs"

 home_sends_reply_to_client_shared: 
 "\<lbrakk>tr:traces cs; home_sends_reply_to_client_shared_guard  (last tr)  ;
   home_sends_reply_to_client_shared_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:traces cs"  

 home_sends_reply_to_client_exclusive :
 "\<lbrakk>tr:traces cs; home_sends_reply_to_client_exclusive_guard  (last tr) cs;
   home_sends_reply_to_client_exclusive_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:traces cs"

constdefs invariant2 ::  "state \<Rightarrow> client \<Rightarrow> client set \<Rightarrow> bool"
"invariant2 s c cs==(channel3 s c=invalidate_ack& home_exclusive_granted s )
                     \<longrightarrow> (ALL i:cs. (~i=c\<longrightarrow> cache s i~=exclusive & channel2_4 s i~=grant_exclusive&channel3 s i~=invalidate_ack))"

constdefs invariant2_conclusion::"state \<Rightarrow> client \<Rightarrow> client set \<Rightarrow> bool"
"invariant2_conclusion s c cs==(ALL i:cs. ~i=c\<longrightarrow>( cache s i~=exclusive & channel2_4 s i~=grant_exclusive&channel3 s i~=invalidate_ack ))"

consts traces':: "client set  \<Rightarrow>(state list) set "
inductive "traces' cs "
  intros
  Init_trace' [intro]: "(Init_state_spec s cs) \<Longrightarrow> [s]: traces' cs "
  client_requests_shared_access':
   "\<lbrakk>tr:traces' cs ; c:cs;
     client_requests_shared_access_guard (last tr) c;
     client_requests_shared_access_update (last tr) s c     \<rbrakk>\<Longrightarrow>
     tr@[s]:traces' cs "

  client_requests_exclusive_access':"
   \<lbrakk> tr:traces' cs ; c:cs;
     client_requests_exclusive_guard (last tr) c;
     client_requests_exclusive_access_update (last tr) s c \<rbrakk>\<Longrightarrow>
     tr@[s]:traces' cs "
      
  home_picks_new_request':
  "\<lbrakk>tr:traces' cs ; c:cs;
    home_picks_new_request_guard (last tr) c ;
    home_picks_new_request_update (last tr) s c
   \<rbrakk> \<Longrightarrow>  tr@[s]:traces' cs "

  home_sends_invalidate_message':
  "\<lbrakk>tr:traces' cs ; c:cs;
   home_sends_invalidate_message_guard (last tr) c;
   home_sends_invalidate_message_update (last tr) s  c\<rbrakk>\<Longrightarrow>
   tr@[s]:traces' cs "   
 
 home_receives_invalidate_acknowledgement':
  " \<lbrakk>tr:traces' cs ; c:cs;
     invariant2 (last tr) c cs;
     home_receives_invalidate_acknowledgement_guard  (last tr) c;
    home_receives_invalidate_acknowledgement_update (last tr) s c \<rbrakk>\<Longrightarrow> 
    tr@[s]:traces' cs " 


 sharer_invalidates_cache':
 " \<lbrakk>tr:traces' cs ; c:cs; sharer_invalidates_cache_guard (last tr) c;
    sharer_invalidates_cache_update (last tr) s c\<rbrakk>\<Longrightarrow>
        tr@[s]:traces' cs "

 client_receives_shared_grant':
 "\<lbrakk>tr:traces' cs ; c:cs; client_receives_shared_grant_guard (last tr) c;
   client_receives_shared_grant_update (last tr) s c \<rbrakk>\<Longrightarrow>
        tr@[s]:traces' cs "
            
 client_receives_exclusive_grant':
  "\<lbrakk>tr:traces' cs ; c:cs; client_receives_exclusive_grant_guard (last tr) c  ;
     client_receives_exclusive_grant_update (last tr) s c\<rbrakk>\<Longrightarrow>
     tr@[s]:traces' cs "

 home_sends_reply_to_client_shared': 
 "\<lbrakk>tr:traces' cs ; home_sends_reply_to_client_shared_guard  (last tr)  ;
   home_sends_reply_to_client_shared_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:traces' cs "  

 home_sends_reply_to_client_exclusive' :
 "\<lbrakk>tr:traces' cs ; home_sends_reply_to_client_exclusive_guard  (last tr) cs;
   home_sends_reply_to_client_exclusive_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:traces' cs "

   
 
consts abs_traces1:: "client set \<Rightarrow>client\<Rightarrow> (state list) set"
inductive "abs_traces1 cs cur "
  intros
  Init_trace_comm [intro]: "Init_state_spec s (cs Un {cur})  \<Longrightarrow> [s]: abs_traces1 cs cur "

  client_requests_shared_access_comm:
   "\<lbrakk>tr:abs_traces1 cs cur; c:cs;
     client_requests_shared_access_guard (last tr) c;
     client_requests_shared_access_update (last tr) s c     \<rbrakk>\<Longrightarrow>
     tr@[s]:abs_traces1 cs cur"

  client_requests_exclusive_access_comm:"
   \<lbrakk> tr:abs_traces1 cs cur; c:cs;
     client_requests_exclusive_guard (last tr) c;
     client_requests_exclusive_access_update (last tr) s c \<rbrakk>\<Longrightarrow>
     tr@[s]:abs_traces1 cs cur"
      
  home_picks_new_request_comm:
  "\<lbrakk>tr:abs_traces1 cs cur; c:(cs );    
    home_picks_new_request_guard (last tr) c ;
    
    home_picks_new_request_update (last tr) s c
   \<rbrakk> \<Longrightarrow>  tr@[s]:abs_traces1 cs cur"

  home_picks_new_request_abs:
  "\<lbrakk>tr:abs_traces1 cs cur; 
    home_current_command (last tr) =empty_message;
    home_picks_new_request_update_abs (last tr) s cur
   \<rbrakk> \<Longrightarrow>  tr@[s]:abs_traces1 cs cur"

 
  home_sends_invalidate_message_comm:
  "\<lbrakk>tr:abs_traces1 cs cur; c:(cs Un {cur} );
   home_sends_invalidate_message_guard (last tr) c;
   home_sends_invalidate_message_update (last tr) s  c\<rbrakk>\<Longrightarrow>
   tr@[s]:abs_traces1 cs cur"   
 
 home_receives_invalidate_acknowledgement_comm:
  " \<lbrakk>tr:abs_traces1 cs cur; c:(cs );
     home_receives_invalidate_acknowledgement_guard  (last tr) c;
    (* revision 06/04/19 invaiant2 (last tr) c (cs Un {cur} ); this condition has been discarded*)
    home_receives_invalidate_acknowledgement_update (last tr) s c \<rbrakk>\<Longrightarrow> 
    tr@[s]:abs_traces1 cs cur"

  home_receives_invalidate_acknowledgement_abs:
  " \<lbrakk>tr:abs_traces1 cs cur;
     invariant2_conclusion (last tr) c cs; 
     home_current_command (last tr)~=empty_message;
    home_receives_invalidate_acknowledgement_update (last tr) s c \<rbrakk>\<Longrightarrow> 
    tr@[s]:abs_traces1 cs cur" 

 sharer_invalidates_cache_comm:
 " \<lbrakk>tr:abs_traces1 cs cur; c:(cs Un {cur}); sharer_invalidates_cache_guard (last tr) c;
    sharer_invalidates_cache_update (last tr) s c\<rbrakk>\<Longrightarrow>
        tr@[s]:abs_traces1 cs cur"

 client_receives_shared_grant_comm:
 "\<lbrakk>tr:abs_traces1 cs cur; c:(cs Un {cur}); client_receives_shared_grant_guard (last tr) c;
   client_receives_shared_grant_update (last tr) s c \<rbrakk>\<Longrightarrow>
        tr@[s]:abs_traces1 cs cur"
            
 client_receives_exclusive_grant_comm:
  "\<lbrakk>tr:abs_traces1 cs cur; c:(cs Un {cur}); client_receives_exclusive_grant_guard (last tr) c ;
     client_receives_exclusive_grant_update (last tr) s c\<rbrakk>\<Longrightarrow>
     tr@[s]:abs_traces1 cs cur"

 home_sends_reply_to_client_shared_comm: 
 "\<lbrakk>tr:abs_traces1 cs cur; home_sends_reply_to_client_shared_guard  (last tr) ;
   home_sends_reply_to_client_shared_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:abs_traces1 cs cur"  

 home_sends_reply_to_client_shared_abs: 
 "\<lbrakk>tr:abs_traces1 cs cur; home_current_command  (last tr) =req_shared&~home_exclusive_granted (last tr);
   home_sends_reply_to_client_shared_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:abs_traces1 cs cur"

 home_sends_reply_to_client_exclusive_comm :
 "\<lbrakk>tr:abs_traces1 cs cur; home_sends_reply_to_client_exclusive_guard  (last tr) (cs );
   home_sends_reply_to_client_exclusive_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:abs_traces1 cs cur"

 home_sends_reply_to_client_exclusive_abs: 
 "\<lbrakk>tr:abs_traces1 cs cur;  home_current_command (last tr) = req_exclusive
    & (ALL i: cs. ~ (home_sharer_list (last tr)) i);
   home_sends_reply_to_client_exclusive_update (last tr) s  \<rbrakk>\<Longrightarrow>
   tr@[s]:abs_traces1 cs cur"

constdefs
  trace_casual:: "'a   list\<Rightarrow> ( ('a list \<times> nat) \<times> ('a list \<times> nat)) set "
  "trace_casual tr=={(s,s').(EX x .(s=(tr,x)&s'=(tr,(Suc x))&  x<(length tr - 1)))} "


(*lemma local_view:
assumes a1:"P=\<lambda>s s' i j. channel2_4 s i = channel2_4 (s') j&
                    channel3 s i = channel3 (s') i \<and>
                    home_sharer_list s i = home_sharer_list (s') j \<and>
                     home_invalidate_list s i= home_invalidate_list (s') j&
                    \<and>cache s i = cache (s') j" and
        a2:"P s (last tr) i i"
        a3:"P ?s (last tr1) i*)
axioms channel1_value:"\<lbrakk>tr :traces' cs\<rbrakk>\<Longrightarrow>
  ALL i:cs. channel1 (last tr) i=empty_message|channel1 (last tr) i=req_shared|  channel1 (last tr) i=req_exclusive"

axioms home_current_client_in_cs:"\<lbrakk>tr :traces' cs\<rbrakk>\<Longrightarrow>home_current_command (last tr)~=empty_message\<longrightarrow>home_current_client (last tr):cs"

lemma permutation_exists:
assumes M1:"d1 \<noteq> d2" and M2:" d1 \<in> cs" and M3:" d2 \<in> cs" and
        M4:"c1 \<noteq> c2" and M5:" c1 \<in> cs" and M6:" c2 \<in> cs" 
shows  M7:"EX f.( (ALL x. x :(cs) \<longrightarrow>f x:cs)& (inj f)&
                  (ALL x:cs.(EX y:cs. x=f y))& f c1=d1& f c2=d2)"  (is "EX f. ?Proj f cs &inj f & ?surj f&?map f")
proof(case_tac "c1=d1"  )
assume  M8:"c1 = d1"
let ?f="%x.(if x=c1 then d1
           else if x=c2 then d2
           else if x=d2 then c2
           else x)"
show " \<exists>f. ?Proj f cs &inj f & ?surj f & ?map f"
proof(rule_tac x="?f" in exI,rule conjI)
show "?Proj ?f cs " apply - apply( rule allI,cut_tac M2 M3 M5 M6 M8) apply simp done
next
show "inj ?f&?surj ?f  & ?map ?f" 
proof(rule conjI)
show "inj ?f"  apply - apply(cut_tac M1 M4 M8,unfold inj_on_def)
               apply(rule ballI)+ apply simp apply(case_tac "d2=c2",simp+)
               apply(case_tac "x=d2",simp) apply(subgoal_tac "d2~=d1",simp+)
               apply(rule impI) apply(rule conjI) apply(rule impI, rule conjI)
               apply(rule ccontr) apply simp apply simp apply(rule impI, rule conjI)
               apply(rule impI, rule ccontr, simp) apply(rule impI)+ apply  simp
               apply(rule ccontr,simp) apply simp
               apply((rule impI)+, rule conjI) apply(rule impI, rule ccontr, simp)
                apply((rule impI)+, rule conjI) apply(rule impI, rule ccontr, simp)
                apply( (rule impI)+, rule ccontr,simp)
done
next 
show "?surj ?f  & ?map ?f"
proof(rule conjI)
show "?surj ?f" apply - apply(cut_tac M1 M2 M3 M4 M5 M6 M8, rule ballI,simp)
                     apply(case_tac "x=c1" )apply(rule_tac x=" d1"in bexI , simp+)
                     apply(case_tac "x=c2")apply(rule_tac x=" d2"in bexI , simp+) 
                     apply(rule ccontr,simp+)
                     apply(case_tac "x=d2")apply(rule_tac x=" c2"in bexI , simp+) 
                     apply(rule conjI,(rule ccontr,simp+),(rule ccontr,simp+))
                     apply(rule_tac x=" x"in bexI , simp+)
                done
next
show " ?map ?f" apply - apply (cut_tac M4, auto )  done
qed 
qed
qed
next
assume M9:"c1~=d1"

show " \<exists>f. ?Proj f cs &inj f & ?surj f & ?map f"
proof(case_tac "c2~=d2" )
  assume M10:"c2~=d2"
  show ?thesis
  proof(case_tac "c1=d2")
    assume M11:"c1=d2"
    show ?thesis
      proof(case_tac "c2=d1")
       assume M12:"c2=d1"
       let ?f="%x.(if x=c1 then d1           
           else if x=c2 then d2
           else x)"
       show ?thesis
       proof(rule_tac x="?f" in exI, rule conjI)
         show "?Proj ?f cs"
          apply - apply(cut_tac M1 M2 M3 M4 M5 M6  M9 M10 M11 M12, rule allI, rule impI)
          apply simp done
         next
         show "inj ?f&?surj ?f&?map ?f" 
         proof(rule conjI)
           show "inj ?f"
           apply - apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12,unfold inj_on_def) apply(rule ballI)+
                    apply(simp)  apply(rule conjI,(rule impI)+,simp) 
                    apply((rule impI)+,simp) 
            done
           next
           show "?surj ?f &?map ?f"
           proof
           show "?surj ?f"
           apply - apply(rule ballI) apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12)
           apply(case_tac "x=c1") apply(rule_tac x=" d1"in bexI , simp+)
           apply(case_tac "x=c2") apply(rule_tac x=" d2"in bexI , simp+)
           apply(rule_tac x=" x"in bexI , simp+)
           done
           next 
           show "?map ?f" apply -  apply(cut_tac M4, auto) done
         qed
        qed
      qed 
     next
     assume M12:"c2~=d1"
     let ?f="%x.(if x=c1 then d1           
           else if x=c2 then d2
           else if x=d1 then c2
           else x)"
      show ?thesis
       proof(rule_tac x="?f" in exI, rule conjI)
         show "?Proj ?f cs"
          apply - apply(cut_tac M1 M2 M3 M4 M5 M6  M9 M10 M11 M12, rule allI, rule impI)
          apply simp done
         next
         show "inj ?f&?surj ?f&?map ?f" 
         proof(rule conjI)
           show "inj ?f"
           apply - apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12,unfold inj_on_def) apply(rule ballI)+
                    apply(simp)  apply(rule conjI,(rule impI)+) 
                    apply(rule conjI,(rule impI)+,simp)+ 
                    apply((rule impI)+) apply(rule ccontr, simp)
                    apply((rule impI)+) apply(rule conjI)
                    apply((rule impI)+,simp)+ 
            done
           show "?surj ?f&?map ?f"
           proof
            show "?surj ?f"
           apply - apply(rule ballI) apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12)
           apply(case_tac "x=d1") apply(rule_tac x=" c1"in bexI , simp+)
           apply(case_tac "x=d2") apply(rule_tac x=" c2"in bexI , simp+)
           apply(case_tac "x=c2",rule_tac x="d1 "in bexI , simp+)
           apply(rule ccontr,simp) apply simp
           apply(rule_tac x="x "in bexI , simp+)
           done
             show "?map ?f" apply - apply(cut_tac M4, auto) done
         qed
        qed
      qed 
     qed
     next
     assume M11:"c1~=d2"
     show ?thesis
     proof(case_tac "c2=d1")
       assume M12:"c2=d1"
        let ?f="%x.(if x=c1 then d1           
           else if x=c2 then d2
           else if x=d2 then c1
           else x)"
       show ?thesis
       proof(rule_tac x="?f" in exI, rule conjI)
         show "?Proj ?f cs"
          apply - apply(cut_tac M1 M2 M3 M4 M5 M6  M9 M10 M11 M12, rule allI, rule impI)
          apply simp done
         next
         show "inj ?f&?surj ?f &?map ?f" 
         proof(rule conjI)
           show "inj ?f"
           apply - apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12,unfold inj_on_def) apply(rule ballI)+
                    apply(simp)  apply(rule conjI,(rule impI)+) 
                    apply(rule conjI,(rule impI)+,simp)+ 
                    apply((rule impI)+)  apply(rule conjI)
                    apply((rule impI)+,simp)+
                    apply(rule impI)+
                    apply(rule conjI,rule ccontr,simp) apply((rule impI)+, simp)
                    apply(rule impI) apply(rule conjI)
                    apply(rule impI, rule conjI) apply((rule impI)+, simp)
                    apply(rule impI)+ apply(rule conjI) apply(rule impI, rule ccontr,simp)
                    apply(rule impI, rule ccontr,simp)
                    apply((rule impI)+ ,(rule conjI))+
                    apply(rule impI, rule ccontr,simp) apply(rule impI, rule ccontr,simp)
                    apply(rule impI)+ apply simp
            done
           show "?surj ?f &?map ?f"
           proof
           show "?surj ?f"
           apply - apply(rule ballI) apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12)
           apply(case_tac "x=d1") apply(rule_tac x=" c1"in bexI , simp+)
           apply(case_tac "x=d2") apply(rule_tac x=" c2"in bexI , simp+)
           apply(rule ccontr, simp+)
           apply(case_tac "x=c1",rule_tac x="d2 "in bexI , simp+)
           apply(rule conjI) apply(rule ccontr,simp)
           apply(rule impI,rule ccontr, simp) apply simp
           apply(rule_tac x="x "in bexI , simp+)
           done
           show "?map ?f" apply - apply(cut_tac M4,auto) done
         qed
        qed
      qed 
      next
      assume M12:"~c2=d1"
        let ?f="%x.(if x=c1 then d1           
           else if x=c2 then d2
           else if x=d1 then c2
           else if x=d2 then c1
           else x)"
       show ?thesis
       proof(rule_tac x="?f" in exI, rule conjI)
         show "?Proj ?f cs"
          apply - apply(cut_tac M1 M2 M3 M4 M5 M6  M9 M10 M11 M12, rule allI, rule impI)
          apply simp done
         next
         show "inj ?f&?surj ?f&?map ?f" 
         proof(rule conjI)
           show "inj ?f"
           apply - apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12,unfold inj_on_def) apply(rule ballI)+
                   apply(case_tac "x=c1",simp)
                    apply(rule conjI,(rule impI)+) apply(rule ccontr, simp)
                    apply((rule impI)+,simp)
                    apply(case_tac "x=c2",simp)
                    apply(case_tac "y=d2" ,simp) 
                    apply((rule impI)+,simp+)
                    apply(case_tac "y=d1",simp)
                    apply(rule impI, rule conjI,rule ccontr,simp)
                    apply(rule impI,rule ccontr,simp)
                    apply(case_tac "y=d2",simp) 
                    apply simp
                    apply(rule impI,rule conjI, rule ccontr,simp)
                     apply(rule impI,rule ccontr,simp)
                   
                    apply(case_tac "x=d1",simp)
                     apply(case_tac "y=d2",simp+)
                     apply((rule impI)+,rule ccontr,simp+)
                     apply((rule impI)+,rule ccontr,simp)
                    apply(case_tac "x=d2",simp) 
                    apply((rule impI)+,rule ccontr,simp+)
                    
            done
           show "?surj ?f &?map ?f"
           proof
           show "?surj ?f"
           apply - apply(rule ballI) apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10 M11 M12)
           apply(case_tac "x=d1") apply(rule_tac x=" c1"in bexI , simp+)
           apply(case_tac "x=d2") apply(rule_tac x=" c2"in bexI , simp+)
           apply(rule ccontr, simp+)
           apply(case_tac "x=c2",rule_tac x="d1 "in bexI , simp+)
           apply(rule conjI) apply(rule ccontr,simp)
           apply(rule impI,rule ccontr, simp) apply simp
           apply(case_tac "x=c1",rule_tac x="d2 "in bexI , simp+)
           apply(rule conjI) apply(rule ccontr,simp)
           apply( rule impI,rule conjI, rule ccontr, simp) apply( rule impI, rule ccontr, simp)
           apply simp
           apply(rule_tac x="x "in bexI , simp+)
           done
          show "?map ?f" by(cut_tac M4,auto)
        qed
      qed 
     qed
    qed
  qed
  next
  assume M10:"~c2~=d2"
  from M10  have M10:"c2=d2" by simp
  let ?f="%x.(if x=c1 then d1
           else if x=c2 then d2
           else if x=d1 then c1           else x)"
  show "EX f.?Proj f cs &inj f & ?surj f&?map f"
  proof(rule_tac x="?f" in exI,rule conjI)
  show "?Proj ?f cs " apply - apply( rule allI,cut_tac M2 M3 M5 M6 M10) apply simp done
  next
  show "inj ?f&?surj ?f&?map ?f" 
  proof(rule conjI)
  show "inj ?f"  apply - apply(cut_tac M1 M4  M9  M10,unfold inj_on_def)
               apply(rule ballI)+ apply simp 
               apply(case_tac "x=d1",simp) apply(subgoal_tac "d1~=c1",simp+)
               apply(rule impI)+ apply simp apply(rule ccontr,simp) apply simp+
               apply(case_tac "x=d2",simp) apply(rule impI)+ apply simp
               apply simp+ apply(rule impI)+ apply simp
               
done
next show "?surj ?f&?map ?f"
     proof
     show "?surj ?f"
      apply - 
                     apply(cut_tac M1 M2 M3 M4 M5 M6 M9 M10, rule ballI,simp)
                      
                     apply(case_tac "x=d1") apply(rule_tac x=" c1"in bexI , simp+)
                     apply(case_tac "x=d2") apply(rule_tac x=" c2"in bexI , simp+)
                     apply(rule ccontr, simp+)
                     apply(case_tac "x=c1",rule_tac x="d1 "in bexI , simp+)
                     apply(rule_tac x="x "in bexI , simp+)
                     
                done
   show "?map ?f" by(cut_tac M4,auto)
qed
qed 
qed
qed
qed
  
lemma three_sim_any:
assumes M1:"d1 \<noteq> d2" and M2:" d1 \<in> cs" and M3:" d2 \<in> cs" and M4:"d3:cs"  and
        M5:"~d1=d3"  and M6:"~d2=d3"   and M7:"tr:traces' cs" 

shows "EX tr':(abs_traces1 {d1,d2} d3 ).(state_sim_on (last tr) (last tr') {d1,d2}  &
      (
       home_current_command (last tr) =home_current_command (last tr')&
         home_exclusive_granted (last tr) = home_exclusive_granted (last tr') 
      )&

      ( home_current_command (last tr)~=empty_message &(home_current_client (last tr)):(cs - {d1,d2})\<longrightarrow>
       ( home_current_client (last tr')=d3  ))&

     ( home_current_command (last tr)~=empty_message &home_current_client (last tr):( {d1,d2})\<longrightarrow>
        home_current_client (last tr')=home_current_client (last tr ))
      )"     (is "(EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr  tr'  ))")
using M7
proof induct

fix s

assume N1:"  Init_state_spec s cs"

let ?s="s\<lparr>
          home_current_client:=d3
          \<rparr>"
show " (EX tr':abs_traces1 {d1,d2} d3. (?P1 [s]  tr' &?P2 [s] tr'  ))"
    proof(rule_tac x="[?s]" in bexI )
    show "(?P1 [s]  [?s] &?P2 [s] [?s] )"
     proof
       show "?P1 [s]  [?s] " 
      by(cut_tac N1   M2 M3 M4, unfold Init_state_spec_def  state_sim_on_def, auto)
      next
      show "?P2 [s]  [?s] "  
      apply - apply(cut_tac N1   M2 M3 M4, unfold Init_state_spec_def)
      apply( simp)
     done
    qed
   next
    show "[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule Init_trace_comm,cut_tac N1  M2 M3 M4 , unfold Init_state_spec_def,simp) done
   qed
  
next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:" client_requests_shared_access_guard (last tr) c" and
       N5:" client_requests_shared_access_update (last tr) s c"
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>channel1:=(channel1 (last tr1))(c:=req_shared) \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold  client_requests_shared_access_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  client_requests_shared_access_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_shared_access_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_shared_access_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in client_requests_shared_access_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def client_requests_shared_access_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N4, unfold state_sim_on_def client_requests_shared_access_update_def)
    apply simp+ 
    done
   qed
   }
   moreover
    {assume N7a:"~c:{d1,d2}"
    (*let ?s="la"*)
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold  client_requests_shared_access_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+  
           apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  client_requests_shared_access_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_shared_access_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_shared_access_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp
 qed
   }
 ultimately show ?thesis by blast
qed
next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:" client_requests_exclusive_guard (last tr) c" and
       N5:" client_requests_exclusive_access_update (last tr) s c"
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>channel1:=(channel1 (last tr1))(c:=req_exclusive) \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold  client_requests_exclusive_access_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  client_requests_exclusive_access_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_exclusive_access_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_exclusive_access_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in client_requests_exclusive_access_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def client_requests_exclusive_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N4, unfold state_sim_on_def client_requests_exclusive_access_update_def)
    apply simp+ 
    done
   qed
   }
   moreover
    {assume N7a:"~c:{d1,d2}"
    (*let ?s="la"*)
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold  client_requests_exclusive_access_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+  
           apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  client_requests_exclusive_access_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_exclusive_access_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_requests_exclusive_access_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp
 qed
   }
 ultimately show ?thesis by blast
qed

next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:" home_picks_new_request_guard (last tr) c" and
       N5:" home_picks_new_request_update (last tr) s c"

show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3 & (?P1 tr  tr1 &?P2 tr tr1) "
       by auto
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c :{d1,d2}"
    let ?s="(last tr1)\<lparr>channel1 := (channel1 (last tr1))(c := empty_message),
          home_current_client := c,
          home_current_command := (channel1 (last tr1) c),
          home_invalidate_list := home_sharer_list (last tr1)\<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold  home_picks_new_request_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" apply - apply (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  home_picks_new_request_update_def state_sim_on_def,simp,auto) done
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_picks_new_request_update_def state_sim_on_def,simp)
        next show "?P22" 
        apply - apply (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_picks_new_request_update_def state_sim_on_def,simp+)
        done
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in home_picks_new_request_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def home_picks_new_request_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N4, unfold state_sim_on_def home_picks_new_request_update_def)
    apply (erule disjE) apply simp+ 
    done
   qed     
   }
   moreover
   {assume N7a:"~c:{d1,d2}"
(*revision 06/4/19 -- channel1 d3=emptymessage is discarded to match the revision of home_picks_new_request_abs*)
    let ?s="(last tr1\<lparr>
          home_current_client := d3,
          home_current_command := (channel1 (last tr) c),
          home_invalidate_list := home_sharer_list (last tr1)\<rparr>)"
    have "EX tr':abs_traces1 {d1,d2} d3. (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 N7a M5 M6 ,  unfold  home_picks_new_request_update_def  state_sim_on_def,simp+,rule conjI,rule impI,simp,(rule impI)+, simp) 
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" apply - apply (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  home_picks_new_request_update_def state_sim_on_def,simp) done
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_picks_new_request_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_picks_new_request_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
   
     proof(rule_tac cur="d3"  and cs="{d1,d2}" in home_picks_new_request_abs,simp,
           cut_tac N4, unfold state_sim_on_def home_picks_new_request_guard_def,simp)
     show "home_picks_new_request_update_abs (last tr1) ?s d3 "
       apply - apply(unfold home_picks_new_request_update_abs_def) 
       
       apply(cut_tac channel1_value[where tr="tr" and cs="cs"])
       apply(drule_tac x="c" in bspec) thm N3
       apply( cut_tac N3,simp)
       apply(cut_tac N4, unfold  home_picks_new_request_guard_def ,simp)
       apply(erule disjE,simp+) 
       apply (cut_tac N1,simp ) 

    done
   qed     
qed
}

 ultimately show ?thesis by blast
qed
next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:" home_sends_invalidate_message_guard (last tr) c" and
       N5:" home_sends_invalidate_message_update (last tr) s c"
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>channel2_4:=(channel2_4 (last tr1)) (c:= invalidate),
                   home_invalidate_list:= (home_invalidate_list (last tr1))  (c:=False)   \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold  home_sends_invalidate_message_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  home_sends_invalidate_message_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_invalidate_message_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_invalidate_message_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in home_sends_invalidate_message_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def home_sends_invalidate_message_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N5, unfold state_sim_on_def home_sends_invalidate_message_update_def)
    apply simp+ 
    done
   qed
   }
   moreover
    {assume N7a:"~c:{d1,d2}"
    (*let ?s="la"*)
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold  home_sends_invalidate_message_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+  
           apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  home_sends_invalidate_message_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_invalidate_message_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_invalidate_message_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp
 qed
   }
 ultimately show ?thesis by blast
qed


next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:"  home_receives_invalidate_acknowledgement_guard (last tr) c" and
       N5:"  home_receives_invalidate_acknowledgement_update (last tr) s c" and
       N5':"invariant2 (last tr) c cs"
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>
                      channel3:=(channel3 (last tr1)) (c:= empty_message),
                    home_sharer_list:= (home_sharer_list(last tr1))  (c:=False),
                    home_exclusive_granted:=False  \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold   home_receives_invalidate_acknowledgement_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in  home_receives_invalidate_acknowledgement_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def  home_receives_invalidate_acknowledgement_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N5, unfold state_sim_on_def  home_receives_invalidate_acknowledgement_update_def)
    apply simp+ 
    done
   qed
   }
   moreover
    {assume N7a:"~c:{d1,d2}"
     have "home_exclusive_granted (last tr1) | ~home_exclusive_granted (last tr1)"  by blast
     moreover
     {assume N8:"home_exclusive_granted (last tr1)"
      
(* have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold   home_receives_invalidate_acknowledgement_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21"   by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp) 
                      apply - apply (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 )
                     apply(  unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp) apply simp+
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from N5' N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp 
    
   qed

*)


     let ?s="(last tr1)\<lparr>
                      channel3:=(channel3 (last tr1)) (d3:= empty_message),
                    home_sharer_list:= (home_sharer_list(last tr1))  (d3:=False),
                    home_exclusive_granted:=False  \<rparr>"
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1@[?s]" in bexI )
        show "(?P1 (tr@[s]) (tr1@[?s]) &?P2 (tr@[s]) (tr1@[?s])  )"
        proof
         show "?P1 (tr@[s]) (tr1@[?s] ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold   home_receives_invalidate_acknowledgement_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1@[?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from N5' N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 " 
    apply - apply(rule_tac c="d3" in  home_receives_invalidate_acknowledgement_abs) apply simp
    apply(unfold invariant2_conclusion_def invariant2_def,simp)
    apply(unfold state_sim_on_def, simp)
    apply(cut_tac N8 N4,unfold   home_receives_invalidate_acknowledgement_guard_def,simp)
    apply(frule_tac x="d1" in bspec,cut_tac M2) apply simp
    apply( frule_tac x="d2" in bspec, cut_tac M3,simp, cut_tac M4 M5 M6,simp+)
    apply(drule mp) apply(rule ccontr, simp) apply(drule mp, rule ccontr,simp) apply simp
    apply(cut_tac N4, unfold state_sim_on_def  home_receives_invalidate_acknowledgement_guard_def)
    apply simp+ 
    apply(cut_tac N5, unfold   home_receives_invalidate_acknowledgement_update_def)
    apply simp+ done
   qed
   }
  moreover
   {assume N8:"~home_exclusive_granted (last tr1)"     
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold   home_receives_invalidate_acknowledgement_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" proof (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)qed
                       
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   home_receives_invalidate_acknowledgement_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from N5' N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp 
    
   qed
   }
  ultimately have ?thesis by blast
 }
 ultimately show ?thesis by blast
qed

next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:" sharer_invalidates_cache_guard (last tr) c" and
       N5:" sharer_invalidates_cache_update (last tr) s c" 
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>
                      channel3:=(channel3 (last tr1)) (c:= invalidate_ack),
                      channel2_4:=(channel2_4 (last tr1)) (c:= empty_message),
                      cache:= (cache (last tr1))  (c:=invalid) \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold  sharer_invalidates_cache_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  sharer_invalidates_cache_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  sharer_invalidates_cache_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  sharer_invalidates_cache_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in sharer_invalidates_cache_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def sharer_invalidates_cache_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N5, unfold state_sim_on_def sharer_invalidates_cache_update_def)
    apply simp+ 
    done
   qed
   }
  moreover
   {assume N7a:"~c:{d1,d2}"     
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold   sharer_invalidates_cache_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" proof (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold   sharer_invalidates_cache_update_def state_sim_on_def,simp)qed
                       
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   sharer_invalidates_cache_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   sharer_invalidates_cache_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from  N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp 
    
   qed
   }
  ultimately show ?thesis by blast
 qed
next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:" client_receives_shared_grant_guard (last tr) c" and
       N5:" client_receives_shared_grant_update (last tr) s c" 
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>
                      
                      channel2_4:=(channel2_4 (last tr1)) (c:= empty_message),
                      cache:= (cache (last tr1))  (c:=shared) \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold  client_receives_shared_grant_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  client_receives_shared_grant_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_receives_shared_grant_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_receives_shared_grant_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in client_receives_shared_grant_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def client_receives_shared_grant_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N5, unfold state_sim_on_def client_receives_shared_grant_update_def)
    apply simp+ 
    done
   qed
   }
  moreover
   {assume N7a:"~c:{d1,d2}"     
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold   client_receives_shared_grant_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" proof (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold   client_receives_shared_grant_update_def state_sim_on_def,simp)qed
                       
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   client_receives_shared_grant_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   client_receives_shared_grant_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from  N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp 
    
   qed
   }
  ultimately show ?thesis by blast
 qed
next
fix c s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       N3:"c \<in> cs" and
       N4:" client_receives_exclusive_grant_guard (last tr) c" and
       N5:" client_receives_exclusive_grant_update (last tr) s c" 
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    
    have "c :{d1,d2} |~c:{d1,d2}" by blast
    moreover
    {assume N7a:"c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>
                      
                      channel2_4:=(channel2_4 (last tr1)) (c:= empty_message),
                      cache:= (cache (last tr1))  (c:=exclusive) \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold  client_receives_exclusive_grant_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  client_receives_exclusive_grant_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_receives_exclusive_grant_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  client_receives_exclusive_grant_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule_tac c="c" in client_receives_exclusive_grant_comm, simp, blast)
    apply(cut_tac N4, unfold state_sim_on_def client_receives_exclusive_grant_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N5, unfold state_sim_on_def client_receives_exclusive_grant_update_def)
    apply simp+ 
    done
   qed
   }
  moreover
   {assume N7a:"~c:{d1,d2}"     
     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1" in bexI )
        show "(?P1 (tr@[s]) (tr1) &?P2 (tr@[s]) (tr1)  )"
        proof
         show "?P1 (tr@[s]) (tr1 ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold   client_receives_exclusive_grant_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1)   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" proof (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold   client_receives_exclusive_grant_update_def state_sim_on_def,simp)qed
                       
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   client_receives_exclusive_grant_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold   client_receives_exclusive_grant_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from  N6 N7a  show "tr1:abs_traces1 {d1,d2} d3 " by simp 
    
   qed
   }
  ultimately show ?thesis by blast
 qed
next
fix  s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       
       N4:"home_sends_reply_to_client_shared_guard (last tr) " and
       N5:"home_sends_reply_to_client_shared_update (last tr) s " 
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    let ?c="home_current_client (last tr)"
    have "?c :{d1,d2} |~?c:{d1,d2}" by blast
    moreover
    {assume N7a:"?c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>
                      home_current_command:=empty_message,
                      channel2_4:=(channel2_4 (last tr1)) (?c:= grant_shared),
                      home_sharer_list:= (home_sharer_list (last tr1))  (?c:=True) \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold home_sends_reply_to_client_shared_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold home_sends_reply_to_client_shared_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold home_sends_reply_to_client_shared_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold home_sends_reply_to_client_shared_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule home_sends_reply_to_client_shared_comm) apply simp
    apply(cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_shared_guard_def)
    apply simp+ apply (erule disjE) apply simp+
    apply(cut_tac N5, unfold state_sim_on_def home_sends_reply_to_client_shared_update_def)
    apply(subgoal_tac "?c= home_current_client (last tr1)",simp) 
     apply( (erule conjE)+,cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_shared_guard_def,simp )
    done
   qed
   }
  moreover
   {assume N7a:"~?c:{d1,d2}"  
       
     let ?s="(last tr1)\<lparr>
                      home_current_command:=empty_message,
                      channel2_4:=(channel2_4 (last tr1)) (d3:= grant_shared),
                      home_sharer_list:= (home_sharer_list (last tr1))  (d3:=True) \<rparr>"   

     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1@[?s]" in bexI )
        show "(?P1 (tr@[s]) (tr1@[?s]) &?P2 (tr@[s]) (tr1@[?s])  )"
        proof
         show "?P1 (tr@[s]) (tr1@[?s] ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold  home_sends_reply_to_client_shared_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1@[?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" proof (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  home_sends_reply_to_client_shared_update_def state_sim_on_def,simp)qed
                       
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_reply_to_client_shared_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_reply_to_client_shared_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from  N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "  
    apply - apply(rule home_sends_reply_to_client_shared_abs) apply simp
    apply(cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_shared_guard_def)
    apply simp+
    apply(cut_tac N5, unfold state_sim_on_def home_sends_reply_to_client_shared_update_def)
    apply(subgoal_tac " home_current_command (last tr) \<noteq> empty_message \<and> home_current_client (last tr) \<in> cs",simp) 
     apply( cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_shared_guard_def )
     apply(cut_tac home_current_client_in_cs[where tr="tr" and cs="cs"],simp) 
     apply assumption
    done
   qed
   
   }
  ultimately show ?thesis by blast
 qed

next
fix  s tr
assume N1:"tr \<in> traces' cs" and        
       N2:" (EX tr':abs_traces1 {d1,d2} d3. (?P1 tr  tr' &?P2 tr tr'  ))" and
       
       N4:"home_sends_reply_to_client_exclusive_guard (last tr) cs" and
       N5:"home_sends_reply_to_client_exclusive_update (last tr) s " 
show "(EX tr':abs_traces1 {d1,d2} d3 . ( ?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr'  ))"
   
  proof -
    from N2 obtain tr1 where N6:"tr1:abs_traces1 {d1,d2} d3  &?P1 tr  tr1 &?P2 tr tr1  " by auto (*ask *)
    let ?c="home_current_client (last tr)"
    have "?c :{d1,d2} |~?c:{d1,d2}" by blast
    moreover
    {assume N7a:"?c:{d1,d2}"     
    let ?s="(last tr1)\<lparr>home_exclusive_granted:=True,
                      home_current_command:=empty_message,
                      channel2_4:=(channel2_4 (last tr1)) (?c:= grant_exclusive),
                      home_sharer_list:= (home_sharer_list (last tr1))  (?c:=True) \<rparr>"    
    have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
    proof(rule_tac x="tr1@[?s]" in bexI )
    show "(?P1 (tr@[s]) (tr1@ [?s]) &?P2 (tr@[s]) (tr1@ [?s])  )"
     proof
       show "?P1 (tr@[s]) (tr1@ [?s]) " 
       apply - apply(cut_tac N5 N6 ,  unfold home_sends_reply_to_client_exclusive_update_def  state_sim_on_def, simp)
        done
      next
      show "?P2 (tr@[s]) (tr1@ [?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" apply - apply(cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold home_sends_reply_to_client_exclusive_update_def state_sim_on_def,simp) done
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold home_sends_reply_to_client_exclusive_update_def state_sim_on_def,simp)
        next show "?P22" (is "?P21 ")
        
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold home_sends_reply_to_client_exclusive_update_def state_sim_on_def,simp)
      qed
    qed
   qed
   next
    from N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "
    apply - apply(rule home_sends_reply_to_client_exclusive_comm) apply simp
    apply(cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_exclusive_guard_def)
    apply simp+ apply (cut_tac M2 M3 ,case_tac "?c=d1",simp,case_tac "?c=d2",simp) apply simp+ 
    
    apply(cut_tac N5, unfold state_sim_on_def home_sends_reply_to_client_exclusive_update_def)
    apply(subgoal_tac "?c= home_current_client (last tr1)",simp) 
     apply( (erule conjE)+,cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_exclusive_guard_def,simp )
    done
   qed
   }
  moreover
   {assume N7a:"~?c:{d1,d2}"  
       
     let ?s="(last tr1)\<lparr>home_exclusive_granted:=True,
                      home_current_command:=empty_message,
                      channel2_4:=(channel2_4 (last tr1)) (d3:= grant_exclusive),
                      home_sharer_list:= (home_sharer_list (last tr1))  (d3:=True) \<rparr>"   

     have "EX tr':abs_traces1 {d1,d2} d3 . (?P1 (tr@[s])  tr' &?P2 (tr@[s]) tr' )"
        proof(rule_tac x="tr1@[?s]" in bexI )
        show "(?P1 (tr@[s]) (tr1@[?s]) &?P2 (tr@[s]) (tr1@[?s])  )"
        proof
         show "?P1 (tr@[s]) (tr1@[?s] ) " 
          apply - 
          apply(cut_tac N5 N6 N7a,  unfold  home_sends_reply_to_client_exclusive_update_def  state_sim_on_def)    
           apply(cut_tac M2 M3 M4 M5 M6 ) apply simp+   
            apply(rule conjI,rule impI, simp,(rule impI)+, simp) done
        next
        show "?P2 (tr@[s]) (tr1@[?s])   "  (is "?P21 &?P22")
      proof(rule conjI)
        show "?P21" proof (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6 ,
                       unfold  home_sends_reply_to_client_exclusive_update_def state_sim_on_def,simp)qed
                       
        next show "?P22" (is "?P21 &?P22")
        proof
        show "?P21"
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_reply_to_client_exclusive_update_def state_sim_on_def,simp)
        next show "?P22" 
        by (cut_tac N5 N6 N7a  M2 M3 M4 M5 M6  ,
                       unfold  home_sends_reply_to_client_exclusive_update_def state_sim_on_def,simp)
        
      qed
    qed
   qed
   next
    from  N6 N7a  show "tr1@[?s]:abs_traces1 {d1,d2} d3 "  
    apply - apply(rule home_sends_reply_to_client_exclusive_abs) apply simp
    apply(cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_exclusive_guard_def)
    apply (cut_tac M2 M3,simp+)
    apply(cut_tac N5, unfold state_sim_on_def home_sends_reply_to_client_exclusive_update_def)
    apply(subgoal_tac " home_current_command (last tr) \<noteq> empty_message \<and> home_current_client (last tr) \<in> cs",simp) 
     apply( cut_tac N4, unfold state_sim_on_def home_sends_reply_to_client_exclusive_guard_def )
      apply(cut_tac home_current_client_in_cs[where tr="tr" and cs="cs"],simp) 
     apply assumption
    done
   qed
   
   }
  ultimately show ?thesis by blast
 qed
qed

lemma sym_cache_term:
assumes (*M1:"d1 \<noteq> d2" and M2:" d1 \<in> cs" and M3:" d2 \<in> cs" and
        M4:"c1 \<noteq> c2" and M5:" c1 \<in> cs" and M6:" c2 \<in> cs" and*)
 M7:"(ALL x. x :(cs) \<longrightarrow>f x:cs)& (inj f)&
     (ALL x:cs.(EX y:cs. x=f y))" and 
 M8:"tr:traces' cs"

shows "EX tr':traces' cs. length tr'=length tr &  state_permutating (last tr) (last tr') f cs
                        " ( is "EX tr':traces' cs. ?P  tr' tr")
thm Init_trace
using M8
proof induct
fix s
assume N1:"Init_state_spec s cs"

let ?s'="s\<lparr>home_current_client:=( f) (home_current_client s)\<rparr>"
from   M7 N1  have N2:"Init_state_spec ?s' cs" by (unfold  Init_state_spec_def,auto)
   
show "EX tr':traces' cs. ?P tr' [s] "   
proof (rule_tac x="[?s' ]" in  bexI)
 
 show "length [?s'] = length [s] \<and> state_permutating (last [s]) (last [?s']) f cs"
    (is "?A &?B")
 proof(rule conjI)
  
  show "?A"  by simp
  
  next
  
  from  M7 N1 show "?B"   
  apply -  apply (unfold   state_permutating_def,simp )
  apply(rule ballI) apply (unfold   Init_state_spec_def )
  apply(rule conjI, simp+) done
qed
 next
 from N2 show "[?s']:traces' cs" thm Init_trace by(rule Init_trace') 
qed
 
next

 fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f cs           "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:" client_requests_shared_access_guard (last tra) c" (is "?R1 tra c") and
        N4:"client_requests_shared_access_update (last tra) s c" (is "?R2 tra s c")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -

 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold client_requests_shared_access_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel1:=(channel1 (last tr'))( (f c):=req_shared) \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold client_requests_shared_access_update_def  client_requests_shared_access_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="?f c" and  s="?s'" in  client_requests_shared_access' )
  apply simp  prefer 2 apply assumption prefer 2 apply assumption  apply auto done

 from N4 have N8:"s=(last  tra) \<lparr>channel1:=(channel1 (last tra))( ( c):=req_shared) \<rparr>"
  apply - apply(unfold client_requests_shared_access_update_def) apply auto done

 with N5 M7 N3   have N9:"state_permutating s  ?s' f cs" 
   apply - apply(unfold state_permutating_def client_requests_shared_access_update_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed
next
fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f cs           "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:" client_requests_exclusive_guard (last tra) c" (is "?R1 tra c") and
        N4:"client_requests_exclusive_access_update (last tra) s c" (is "?R2 tra s c")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold client_requests_exclusive_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel1:=(channel1 (last tr'))( (f c):=req_exclusive) \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold client_requests_exclusive_access_update_def  client_requests_exclusive_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="?f c" and  s="?s'" in  client_requests_exclusive_access' )
  apply simp  prefer 2 apply assumption prefer 2 apply assumption  apply auto done

 from N4 have N8:"s=(last  tra) \<lparr>channel1:=(channel1 (last tra))( ( c):=req_exclusive) \<rparr>"
  apply - apply(unfold client_requests_exclusive_access_update_def) apply auto done

 with N5 M7 N3   have N9:"state_permutating s  ?s' f cs" 
   apply - apply(unfold state_permutating_def client_requests_exclusive_access_update_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp 
qed
qed
next
 fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f  cs          "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:" home_picks_new_request_guard (last tra) c" (is "?R1 tra c") and
        N4:"home_picks_new_request_update (last tra) s c" (is "?R2 tra s c")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold home_picks_new_request_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel1:=(channel1 (last tr'))( (f c):=empty_message),
                     home_current_client:=(f c),
                     home_current_command:=(channel1 (last tr') (f c)),
                     home_invalidate_list:=( home_sharer_list (last tr')) \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold home_picks_new_request_update_def  home_picks_new_request_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="?f c" and  s="?s'" in  home_picks_new_request' )
  apply simp  prefer 2 apply assumption prefer 2 apply assumption  apply auto done

 from N4 have N8:"s=(last  tra) \<lparr>channel1:=(channel1 (last tra))( ( c):=empty_message),
                     home_current_client:=( c),
                      home_current_command:=(channel1 (last tra) ( c)),
                     home_invalidate_list:=( home_sharer_list (last tra)) \<rparr>"
  apply - apply(unfold home_picks_new_request_update_def) apply auto done

 with N5 M7 N3  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed
next
 fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f  cs          "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:"home_sends_invalidate_message_guard (last tra) c" (is "?R1 tra c") and
        N4:"home_sends_invalidate_message_update (last tra) s c" (is "?R2 tra s c")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold home_sends_invalidate_message_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel2_4:=(channel2_4 (last tr')) ( (f c):=invalidate),
                     
                     home_invalidate_list:= (home_invalidate_list (last tr')) ( (f c):=False)   \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold home_sends_invalidate_message_update_def  
                  home_sends_invalidate_message_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="?f c" and  s="?s'" in  home_sends_invalidate_message' )
  apply simp  prefer 2 apply assumption prefer 2 apply assumption  apply auto done

 from N4 have N8:"s=(last  tra) \<lparr>channel2_4:=(channel2_4 (last tra)) ( ( c):=invalidate),
                     
                     home_invalidate_list:= (home_invalidate_list (last tra)) ( ( c):=False)  \<rparr>"
  apply - apply(unfold home_sends_invalidate_message_update_def) apply auto done

 with N5 M7 N3  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed

next
 fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f   cs         "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:"home_receives_invalidate_acknowledgement_guard (last tra) c" (is "?R1 tra c") and
        N4:"home_receives_invalidate_acknowledgement_update (last tra) s c" (is "?R2 tra s c") and
        N4a:"invariant2 (last tra) c cs"
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold home_receives_invalidate_acknowledgement_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel3:=(channel3 ( last tr')) ( (f c):= empty_message),
                    home_sharer_list:= (home_sharer_list (last tr'))  ( (f c):=False), 
                   home_exclusive_granted:=False  \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold home_receives_invalidate_acknowledgement_update_def  
                  home_receives_invalidate_acknowledgement_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3 N4a have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="f c" and  s="?s'" in  home_receives_invalidate_acknowledgement' )
  apply simp   prefer 2 apply(unfold invariant2_def state_permutating_def,rule impI)
  apply(drule mp)
  apply(erule conjE)+ apply(drule_tac x="c" in bspec,simp)
  apply simp apply (rule ballI, (rule impI)+) 
  apply(subgoal_tac "EX c':cs. i=f c' & c'~=c") 
  apply(erule bexE) apply(drule_tac x="c'" in bspec)
  apply assumption  apply simp  
  apply(thin_tac "\<forall>i\<in>cs. i \<noteq> c \<longrightarrow>
                cache (last tra) i \<noteq> exclusive \<and> channel2_4 (last tra) i \<noteq> grant_exclusive \<and> channel3 (last tra) i \<noteq> invalidate_ack"
        )
  apply(rotate_tac 1,(erule conjE)+, drule_tac x=" i" in bspec) apply simp   
  apply(erule bexE) apply(subgoal_tac "y~=c")  prefer 2  apply(rule ccontr) apply simp 
  apply(rule_tac x="y" in bexI) apply simp+   done

 from N4 have N8:"s=(last  tra) \<lparr>channel3:=(channel3 ( last tra)) ( ( c):= empty_message),
                    home_sharer_list:= (home_sharer_list (last tra))  ( ( c):=False),
                     home_exclusive_granted:=False   \<rparr>"
  apply - apply(unfold home_receives_invalidate_acknowledgement_update_def) apply auto done

 with N5 M7 N3  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed

next
 fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f  cs          "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:"sharer_invalidates_cache_guard (last tra) c" (is "?R1 tra c") and
        N4:"sharer_invalidates_cache_update (last tra) s c" (is "?R2 tra s c")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold sharer_invalidates_cache_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel2_4:=(channel2_4 (last tr')) ( (f c):= empty_message),
                        channel3:=(channel3 (last tr')) ((f c):= invalidate_ack),
                        cache:=(cache (last tr')) (( f c):= invalid)   \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold sharer_invalidates_cache_update_def  
                  sharer_invalidates_cache_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="?f c" and  s="?s'" in  sharer_invalidates_cache' )
  apply simp  prefer 2 apply assumption prefer 2 apply assumption  apply auto done

 from N4 have N8:"s=(last  tra) \<lparr> 
                       channel2_4:=(channel2_4 (last tra)) ( ( c):= empty_message),
                        channel3:=(channel3 (last tra)) (( c):= invalidate_ack),
                        cache:=(cache (last tra)) ((  c):= invalid)  \<rparr>"
  apply - apply(unfold sharer_invalidates_cache_update_def) apply auto done

 with N5 M7 N3  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed

next
 fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f  cs          "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:"client_receives_shared_grant_guard (last tra) c" (is "?R1 tra c") and
        N4:"client_receives_shared_grant_update (last tra) s c" (is "?R2 tra s c")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold client_receives_shared_grant_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel2_4:=(channel2_4 (last tr')) ( (f c):= empty_message),
                      
                        cache:=(cache (last tr')) (( f c):= shared)   \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold client_receives_shared_grant_update_def  
                  client_receives_shared_grant_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="?f c" and  s="?s'" in  client_receives_shared_grant' )
  apply simp  prefer 2 apply assumption prefer 2 apply assumption  apply auto done

 from N4 have N8:"s=(last  tra) \<lparr> 
                       channel2_4:=(channel2_4 (last tra)) ( ( c):= empty_message),
                        
                        cache:=(cache (last tra)) ((  c):= shared)  \<rparr>"
  apply - apply(unfold client_receives_shared_grant_update_def) apply auto done

 with N5 M7 N3  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed

next
fix c s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f  cs          "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
        N3:"c \<in> cs" and 
        N3a:"client_receives_exclusive_grant_guard (last tra) c" (is "?R1 tra c") and
        N4:"client_receives_exclusive_grant_update (last tra) s c" (is "?R2 tra s c")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with N3 N3a  N5  M7  have N6:" ?R1 ( tr') (f c)"  
   by (unfold client_receives_exclusive_grant_guard_def state_permutating_def,auto)
 
 let ?s'="(last tr') \<lparr>channel2_4:=(channel2_4 (last tr')) ( (f c):= empty_message),
                      
                        cache:=(cache (last tr')) (( f c):= exclusive)   \<rparr>"
  from N5 N3 N4 N3a 
     have " ?R2  ( tr') ?s'  (f c)"  
   apply - apply (unfold client_receives_exclusive_grant_update_def  
                  client_receives_exclusive_grant_guard_def
                  state_permutating_def,
                  auto) done

 with N5 N6 M7 N3  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac c="?f c" and  s="?s'" in  client_receives_exclusive_grant' )
  apply simp  prefer 2 apply assumption prefer 2 apply assumption  apply auto done

 from N4 have N8:"s=(last  tra) \<lparr> 
                       channel2_4:=(channel2_4 (last tra)) ( ( c):= empty_message),
                        
                        cache:=(cache (last tra)) ((  c):= exclusive)  \<rparr>"
  apply - apply(unfold client_receives_exclusive_grant_update_def) apply auto done

 with N5 M7 N3  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed
next
fix  s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f  cs          "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
       
        N3a:"home_sends_reply_to_client_shared_guard (last tra) " (is "?R1 tra ") and
        N4:"home_sends_reply_to_client_shared_update (last tra) s " (is "?R2 tra s ")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with  N3a  N5  M7  have N6:" ?R1 ( tr') "  
   apply - apply (unfold home_sends_reply_to_client_shared_guard_def state_permutating_def,auto)
   apply(cut_tac home_current_client_in_cs[where tr="tra" and cs="cs"])
   apply simp+ apply assumption done
 
 let ?s'="(last tr') \<lparr>channel2_4:=(channel2_4 (last tr')) ( (home_current_client (last tr')):= grant_shared),
                 home_sharer_list:= (home_sharer_list (last tr'))  ((home_current_client (last tr')):=True),
                     home_current_command:=empty_message
                           \<rparr>"
  from N5  N4 N3a 
     have " ?R2  ( tr') ?s'  "  
   apply - apply (unfold home_sends_reply_to_client_shared_update_def  
                  home_sends_reply_to_client_shared_guard_def
                  state_permutating_def,simp) 
            done

 with N5 N6 M7  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac   s="?s'" in  home_sends_reply_to_client_shared' )
  apply simp  prefer 2 apply assumption  apply assumption   done

 from N4 have N8:"s=(last  tra) \<lparr> channel2_4:=(channel2_4 (last tra)) ( (home_current_client (last tra)):= grant_shared),
                 home_sharer_list:= (home_sharer_list (last tra))  ((home_current_client (last tra)):=True),
                     home_current_command:=empty_message
                         \<rparr>"
  apply - apply(unfold home_sends_reply_to_client_shared_update_def) apply auto done

 with N5 M7  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed
next
fix  s tra
 assume N1: "tra \<in> traces' cs" and
        N2:"\<exists>tr'\<in>traces' cs.
           length tr' = length tra \<and>
           state_permutating (last tra) (last tr') f  cs          "
           (is "EX tr':traces' cs. ?P1  tra tr'") and
       
        N3a:"home_sends_reply_to_client_exclusive_guard (last tra) cs " (is "?R1 tra ") and
        N4:"home_sends_reply_to_client_exclusive_update (last tra) s " (is "?R2 tra s ")
 show "\<exists>tr'\<in>traces' cs. ?P tr'  (tra@[s])  "
proof -
 from N2 obtain tr' where N5:"tr':traces' cs& ?P1 tra tr'" by blast
 with  N3a  N5  M7  have N6:" ?R1 ( tr') "  
   apply - apply (unfold home_sends_reply_to_client_exclusive_guard_def state_permutating_def,simp)
   apply(cut_tac home_current_client_in_cs[where tr="tra" and cs="cs"])
   apply simp+ apply(rule ballI) apply(erule conjE)+ 
   apply(subgoal_tac "EX y:cs.(i=f y)") apply(erule bexE)
   apply(drule_tac  x="y" in  bspec) apply  simp+  
   apply assumption done
 
 let ?s'="(last tr') \<lparr>channel2_4:=(channel2_4 (last tr')) ( (home_current_client (last tr')):= grant_exclusive),
                 home_sharer_list:= (home_sharer_list (last tr'))  ((home_current_client (last tr')):=True),
                     home_current_command:=empty_message,
                     home_exclusive_granted:=True
                           \<rparr>"
  from N5  N4 N3a 
     have " ?R2  ( tr') ?s'  "  
   apply - apply (unfold home_sends_reply_to_client_exclusive_update_def  
                  home_sends_reply_to_client_exclusive_guard_def
                  state_permutating_def,simp) 
            done

 with N5 N6 M7  have N7: "tr'@[?s']:traces' cs"
  apply - apply(rule_tac   s="?s'" in  home_sends_reply_to_client_exclusive' )
  apply simp  prefer 2 apply assumption  apply assumption   done

 from N4 have N8:"s=(last  tra) \<lparr> channel2_4:=(channel2_4 (last tra)) ( (home_current_client (last tra)):= grant_exclusive),
                 home_sharer_list:= (home_sharer_list (last tra))  ((home_current_client (last tra)):=True),
                     home_current_command:=empty_message,  home_exclusive_granted:=True
                         \<rparr>"
  apply - apply(unfold home_sends_reply_to_client_exclusive_update_def) apply auto done

 with N5 M7  have N9:"state_permutating s  ?s' f cs" apply - apply(unfold state_permutating_def)
  apply( (simp add:inj_eq))+ done
 show ?thesis
proof(rule_tac x="tr'@[?s']" in bexI)
   from N5 N7 N8 N9 show " length (tr'@[?s']) = length (tra @ [s]) \<and>
       state_permutating (last (tra @ [s])) (last (tr'@[?s'])) f cs"
     apply - apply simp done
   next 
  from N7 show "tr' @ [?s']:traces' cs" by simp
qed
qed
qed

lemma trace_is_trace':
assumes a1:"tr:traces cs"  and a2:"ALL c:cs. (ALL tr:traces' cs. invariant2 (last tr) c cs)"
shows "EX tr':traces' cs. (state_sim_on (last tr) (last tr') cs &
                           
       home_current_command (last tr) =home_current_command (last tr')&
       home_exclusive_granted (last tr) = home_exclusive_granted (last tr') &
     
        home_current_client (last tr)=home_current_client (last tr' ))" (is "EX tr':traces' cs. ?P tr tr' cs")
using a1
proof induct        
fix s
assume M1:"Init_state_spec s cs"
show "EX tr':traces' cs. ?P [s]  tr' cs"
proof(rule_tac x="[s]" in bexI)
 show "?P [s]  [s] cs" by(unfold state_sim_on_def, auto)
 next
 from M1 show "[s] \<in> traces' cs"proof(rule Init_trace') qed
qed
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:" client_requests_shared_access_guard (last tr) c" and
       M5:" client_requests_shared_access_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel1:=(channel1 (last tr'))(c:=req_shared)\<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def client_requests_shared_access_update_def,auto)
    done
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule client_requests_shared_access')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show "client_requests_shared_access_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def client_requests_shared_access_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show "client_requests_shared_access_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def client_requests_shared_access_guard_def
            client_requests_shared_access_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
  qed
 qed
qed
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:" client_requests_exclusive_guard (last tr) c" and
       M5:" client_requests_exclusive_access_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel1:=(channel1 (last tr'))(c:=req_exclusive)\<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def client_requests_exclusive_access_update_def,auto)
    done
 next
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule client_requests_exclusive_access')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show "client_requests_exclusive_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def client_requests_exclusive_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show "client_requests_exclusive_access_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def client_requests_exclusive_guard_def
            client_requests_exclusive_access_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
  qed
 qed
qed
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:" home_picks_new_request_guard (last tr) c" and
       M5:" home_picks_new_request_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel1 := (channel1 ( last tr'))(c := empty_message),
          home_current_client := c,
          home_current_command := (channel1 (last tr') c),
          home_invalidate_list := home_sharer_list (last tr')\<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def home_picks_new_request_update_def,auto)
    done
 next
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule home_picks_new_request')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show "home_picks_new_request_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def home_picks_new_request_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show "home_picks_new_request_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def home_picks_new_request_guard_def
            home_picks_new_request_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
  qed
 qed
qed
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:"  home_sends_invalidate_message_guard (last tr) c" and
       M5:"  home_sends_invalidate_message_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel2_4:=(channel2_4 (last tr')) (c:= invalidate),
                   home_invalidate_list:= (home_invalidate_list(last tr'))  (c:=False)\<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def  home_sends_invalidate_message_update_def,auto)
    done
 next
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule  home_sends_invalidate_message')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show " home_sends_invalidate_message_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_invalidate_message_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show " home_sends_invalidate_message_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_invalidate_message_guard_def
             home_sends_invalidate_message_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
  qed
 qed
qed

next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:" home_receives_invalidate_acknowledgement_guard (last tr) c" and
       M5:" home_receives_invalidate_acknowledgement_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel3:=(channel3 (last tr')) (c:= empty_message),
                    home_sharer_list:= (home_sharer_list(last tr'))  (c:=False),
                    home_exclusive_granted:=False\<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def home_receives_invalidate_acknowledgement_update_def,auto)
    done
 next
    show "(tr'@[?s]) \<in> traces' cs" (*ask*)
    proof(rule home_receives_invalidate_acknowledgement') 
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show "home_receives_invalidate_acknowledgement_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def home_receives_invalidate_acknowledgement_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show "home_receives_invalidate_acknowledgement_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def home_receives_invalidate_acknowledgement_guard_def
            home_receives_invalidate_acknowledgement_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next show "invariant2 (last tr') c cs"
      apply - apply(cut_tac a2) apply(drule_tac x="c" in bspec )
              apply(cut_tac M3,simp, drule_tac x="tr'" in bspec, cut_tac N1,simp+) 
      done
   
  qed
 qed
qed
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:" sharer_invalidates_cache_guard (last tr) c" and
       M5:" sharer_invalidates_cache_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel2_4:=(channel2_4 (last tr')) (c:= empty_message),
                        channel3:=(channel3 (last tr')) (c:= invalidate_ack),
                        cache:=(cache (last tr')) (c:= invalid)\<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def sharer_invalidates_cache_update_def,auto)
    done
 next
 
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule sharer_invalidates_cache')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show "sharer_invalidates_cache_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def sharer_invalidates_cache_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show "sharer_invalidates_cache_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def sharer_invalidates_cache_guard_def
            sharer_invalidates_cache_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
  qed
 qed
qed
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:" client_receives_shared_grant_guard (last tr) c" and
       M5:" client_receives_shared_grant_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel2_4:=(channel2_4 (last tr')) (c:= empty_message),                        
                        cache:=(cache (last tr')) (c:= shared) \<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def client_receives_shared_grant_update_def,auto)
    done
 next
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule client_receives_shared_grant')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show "client_receives_shared_grant_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def client_receives_shared_grant_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show "client_receives_shared_grant_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def client_receives_shared_grant_guard_def
           client_receives_shared_grant_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
  qed
 qed
qed

next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M3:" c \<in> cs" and M4:" client_receives_exclusive_grant_guard (last tr) c" and
       M5:" client_receives_exclusive_grant_update (last tr) s c"
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel2_4:=(channel2_4 (last tr')) (c:= empty_message),                        
                        cache:=(cache (last tr')) (c:= exclusive) \<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1 M3 M5 , unfold state_sim_on_def client_receives_exclusive_grant_update_def,auto)
    done
 next
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule client_receives_exclusive_grant')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 N1 M3 show "client_receives_exclusive_grant_guard (last tr') c" 
      apply - 
      apply(unfold state_sim_on_def client_receives_exclusive_grant_guard_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
      next 
     from M5 N1 M3 M4 show "client_receives_exclusive_grant_update (last tr') ?s c" 
      apply - 
      apply(unfold state_sim_on_def client_receives_exclusive_grant_guard_def
           client_receives_exclusive_grant_update_def)
      apply((erule conjE)+,drule_tac x="c" in bspec) apply simp+ 
      done
  qed
 qed
qed


next
fix  s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M4:"  home_sends_reply_to_client_shared_guard (last tr) " and
       M5:"  home_sends_reply_to_client_shared_update (last tr) s "
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel2_4:= (channel2_4 (last tr')) ((home_current_client (last tr')):= grant_shared),
                home_sharer_list:= (home_sharer_list (last tr'))  ((home_current_client (last tr')):=True),
                 home_current_command:=empty_message  \<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1  M5 , unfold state_sim_on_def  home_sends_reply_to_client_shared_update_def,auto)
    done
 next
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule  home_sends_reply_to_client_shared')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     
     next 
     from M4 N1  show " home_sends_reply_to_client_shared_guard (last tr')" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_shared_guard_def) apply simp
      apply((erule conjE)+,drule_tac x="home_current_client (last tr')" in bspec) 
      thm home_current_client_in_cs  
      apply(drule_tac tr="tr'" in  home_current_client_in_cs) apply simp+ 
      done
      next 
     from M5 N1  M4 show " home_sends_reply_to_client_shared_update (last tr') ?s " 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_shared_guard_def
            home_sends_reply_to_client_shared_update_def)
      apply((erule conjE)+) apply(drule_tac x="home_current_client (last tr')" in bspec)
      apply(drule_tac tr="tr'" in  home_current_client_in_cs, simp+ )
      done
  qed
 qed
qed

next
fix  s tr
assume M1:"tr \<in> traces cs" and
       M2:" \<exists>tr'\<in>traces' cs.
           state_sim_on (last tr) (last tr') cs \<and>
           home_current_command (last tr) = home_current_command (last tr') \<and>
           home_exclusive_granted (last tr) = home_exclusive_granted (last tr') \<and>
           home_current_client (last tr) = home_current_client (last tr')" and
       M4:"  home_sends_reply_to_client_exclusive_guard (last tr) cs" and
       M5:"  home_sends_reply_to_client_exclusive_update (last tr) s "
show "\<exists>tr'\<in>traces' cs. ?P (tr@[s])  tr' cs"
proof -
from M2 obtain tr' where N1:"tr':traces' cs & ?P tr tr' cs" by auto
let ?s="last tr'\<lparr>channel2_4:= (channel2_4 (last tr')) ((home_current_client (last tr')):= grant_exclusive),
                home_sharer_list:= (home_sharer_list (last tr'))  ((home_current_client (last tr')):=True),
                 home_current_command:=empty_message , home_exclusive_granted:=True 
            \<rparr>"
show ?thesis 

proof (rule_tac x="tr'@[?s]" in bexI)
  show "?P (tr@[s])  (tr'@[?s]) cs" 
    apply - apply(cut_tac N1  M5 , unfold state_sim_on_def  home_sends_reply_to_client_exclusive_update_def,auto)
    done
 next
 next
    (*from N1 have N0:"tr':traces' cs" by simp
    from N0 M3 show "(tr'@[?s]) \<in> traces' cs" ask*)
    show "(tr'@[?s]) \<in> traces' cs" 
    proof(rule  home_sends_reply_to_client_exclusive')
      
     from N1 show " tr' \<in> traces' cs" proof( auto) qed
     
     next 
     from M4 N1  show " home_sends_reply_to_client_exclusive_guard (last tr') cs" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_exclusive_guard_def) apply simp
      apply((erule conjE)+,drule_tac x="home_current_client (last tr')" in bspec) 
      thm home_current_client_in_cs  
      apply(drule_tac tr="tr'" in  home_current_client_in_cs) apply simp+ 
      apply(drule_tac x="home_current_client (last tr')" in bspec) 
      thm home_current_client_in_cs  
      apply(drule_tac tr="tr'" in  home_current_client_in_cs) apply simp+ 
      done
      next 
     from M5 N1  M4 show " home_sends_reply_to_client_exclusive_update (last tr') ?s " 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_exclusive_guard_def
            home_sends_reply_to_client_exclusive_update_def)
      apply((erule conjE)+) apply(drule_tac x="home_current_client (last tr')" in bspec)
      apply(drule_tac tr="tr'" in  home_current_client_in_cs, simp+ )
      done
  qed
 qed
qed
qed

lemma trace_is_trace':
assumes a1:"tr:traces cs"  and a2:"ALL c:cs. (ALL tr:traces' cs. invariant2 (last tr) c cs)"
shows " tr:traces' cs"
using a1
proof induct        
fix s
assume M1:"Init_state_spec s cs"
show " [s]:traces' cs"
proof(rule Init_trace') qed

next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" tr:traces' cs" and
       M3:" c \<in> cs" and M4:" client_requests_shared_access_guard (last tr) c" and
       M5:" client_requests_shared_access_update (last tr) s c"
show "tr @ [s]\<in>traces' cs"
 proof(rule client_requests_shared_access')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4  M3 show "client_requests_shared_access_guard (last tr) c" 
      apply - 
      apply(unfold  client_requests_shared_access_guard_def)
       apply simp+ 
      done
      next 
     from M5 M3 M4 show "client_requests_shared_access_update (last tr) s c" 
      apply - 
      apply(unfold  client_requests_shared_access_guard_def
            client_requests_shared_access_update_def)
      apply simp+ 
      done
  qed
 
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:" tr\<in>traces' cs" and       
       M3:" c \<in> cs" and M4:"client_requests_exclusive_guard (last tr) c" and
       M5:" client_requests_exclusive_access_update (last tr) s c"
show " tr @ [s] \<in> traces' cs"
 proof(rule client_requests_exclusive_access')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4  M3 show "client_requests_exclusive_guard (last tr) c" 
      apply - 
      apply(unfold  client_requests_exclusive_guard_def)
      apply simp+ 
      done
      next 
     from M5  M3 M4 show "client_requests_exclusive_access_update (last tr) s c" 
      apply - 
      apply(unfold  client_requests_exclusive_guard_def
            client_requests_exclusive_access_update_def)
      apply simp+ 
      done
  qed
 
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M3:" c \<in> cs" and M4:" home_picks_new_request_guard (last tr) c" and
       M5:" home_picks_new_request_update (last tr) s c"
show "tr @ [s] \<in> traces' cs"

    proof(rule home_picks_new_request')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4  M3 show "home_picks_new_request_guard (last tr) c" 
      apply - 
      apply(unfold  home_picks_new_request_guard_def)
      apply simp+ 
      done
      next 
     from M5  M3 M4 show "home_picks_new_request_update (last tr) s c" 
      apply - 
      apply(unfold  home_picks_new_request_guard_def
            home_picks_new_request_update_def)
       apply simp+ 
      done
  qed
 
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M3:" c \<in> cs" and M4:"  home_sends_invalidate_message_guard (last tr) c" and
       M5:"  home_sends_invalidate_message_update (last tr) s c"
show "tr@[s]:traces' cs"
 proof(rule  home_sends_invalidate_message')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4  M3 show " home_sends_invalidate_message_guard (last tr) c" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_invalidate_message_guard_def)
       apply simp+ 
      done
      next 
     from M5  M3 M4 show " home_sends_invalidate_message_update (last tr) s c" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_invalidate_message_guard_def
             home_sends_invalidate_message_update_def)
       apply simp+ 
      done
  qed
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M3:" c \<in> cs" and M4:" home_receives_invalidate_acknowledgement_guard (last tr) c" and
       M5:" home_receives_invalidate_acknowledgement_update (last tr) s c"
show "tr@[s]:traces' cs"

    proof(rule home_receives_invalidate_acknowledgement') 
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4  M3 show "home_receives_invalidate_acknowledgement_guard (last tr) c" 
      apply - 
      apply(unfold  home_receives_invalidate_acknowledgement_guard_def)
      apply simp+ 
      done
      next 
     from M5  M3 M4 show "home_receives_invalidate_acknowledgement_update (last tr) s c" 
      apply - 
      apply(unfold  home_receives_invalidate_acknowledgement_guard_def
            home_receives_invalidate_acknowledgement_update_def)
      apply simp+ 
      done
      next show "invariant2 (last tr) c cs"
      apply - apply(cut_tac a2) apply(drule_tac x="c" in bspec )
              apply(cut_tac M3,simp)
              apply(drule_tac x="tr" in bspec)
              apply( cut_tac M2,simp+) 
      done
   
  qed
 
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M3:" c \<in> cs" and M4:" sharer_invalidates_cache_guard (last tr) c" and
       M5:" sharer_invalidates_cache_update (last tr) s c"
show "tr@[s]:traces' cs"
proof(rule sharer_invalidates_cache')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4  M3 show "sharer_invalidates_cache_guard (last tr) c" 
      apply - 
      apply(unfold  sharer_invalidates_cache_guard_def)
      apply simp+ 
      done
      next 
     from M5  M3 M4 show "sharer_invalidates_cache_update (last tr) s c" 
      apply - 
      apply(unfold  sharer_invalidates_cache_guard_def
            sharer_invalidates_cache_update_def)
       apply simp+ 
      done
  qed

next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M3:" c \<in> cs" and M4:" client_receives_shared_grant_guard (last tr) c" and
       M5:" client_receives_shared_grant_update (last tr) s c"
show "tr@[s]:traces' cs"
proof(rule client_receives_shared_grant')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4 M2 M3 show "client_receives_shared_grant_guard (last tr) c" 
      apply - 
      apply(unfold  client_receives_shared_grant_guard_def)
       apply simp+ 
      done
      next 
     from M5  M3 M4 show "client_receives_shared_grant_update (last tr) s c" 
      apply - 
      apply(unfold  client_receives_shared_grant_guard_def
           client_receives_shared_grant_update_def)
       apply simp+ 
      done
  qed
 
next
fix c s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M3:" c \<in> cs" and M4:" client_receives_exclusive_grant_guard (last tr) c" and
       M5:" client_receives_exclusive_grant_update (last tr) s c"
show "tr@[s]:traces' cs"
 proof(rule client_receives_exclusive_grant')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     next
     from M3 show "c:cs" by simp
     next 
     from M4  M3 show "client_receives_exclusive_grant_guard (last tr) c" 
      apply - 
      apply(unfold  client_receives_exclusive_grant_guard_def)
      apply simp+ 
      done
      next 
     from M5  M3 M4 show "client_receives_exclusive_grant_update (last tr) s c" 
      apply - 
      apply(unfold client_receives_exclusive_grant_guard_def
           client_receives_exclusive_grant_update_def)
       apply simp+ 
      done
  qed

next
fix  s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M4:"  home_sends_reply_to_client_shared_guard (last tr) " and
       M5:"  home_sends_reply_to_client_shared_update (last tr) s "
show "tr@[s]:traces' cs"
 proof(rule  home_sends_reply_to_client_shared')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     
     next 
     from M4   show " home_sends_reply_to_client_shared_guard (last tr)" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_shared_guard_def) apply simp
      
      done
      next 
     from M5   M4 show " home_sends_reply_to_client_shared_update (last tr) s " 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_shared_guard_def
            home_sends_reply_to_client_shared_update_def) apply simp
      
      done
  qed
 

next
fix  s tr
assume M1:"tr \<in> traces cs" and
       M2:"tr:traces' cs" and
       M4:"  home_sends_reply_to_client_exclusive_guard (last tr) cs" and
       M5:"  home_sends_reply_to_client_exclusive_update (last tr) s "
show "tr@[s]:traces' cs"

    proof(rule  home_sends_reply_to_client_exclusive')
      
     from M2 show " tr \<in> traces' cs" proof( auto) qed
     
     next 
     from M4  show " home_sends_reply_to_client_exclusive_guard (last tr) cs" 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_exclusive_guard_def) apply simp
      done
      next 
     from M5   M4 show " home_sends_reply_to_client_exclusive_update (last tr) s " 
      apply - 
      apply(unfold state_sim_on_def  home_sends_reply_to_client_exclusive_guard_def
            home_sends_reply_to_client_exclusive_update_def)
      apply simp
      done
  qed
 qed


 

lemma sym_prop1:
assumes a0:"c1 ~= c2 & c1:cs&c2:cs" and
        a1:"ALL tr:traces' cs.(
         cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid)" 
shows "
        (ALL tr c1 c2. (tr:traces' cs &c1 ~= c2 & c1:cs&c2:cs&
         cache (last tr) c1 = exclusive)\<longrightarrow> cache (last tr) c2 = invalid)"
proof((rule allI)+, rule impI,(erule conjE)+)
fix tr d1 d2
assume M1:"d1 \<noteq> d2" and M2:" d1 \<in> cs" and M3:" d2 \<in> cs" and
       M4:"cache (last tr) d1 = exclusive" and M5:"tr \<in> traces' cs"
show "cache (last tr) d2 = invalid"
proof -
have N1:"
     EX f.((ALL x. x :(cs) \<longrightarrow>f x:cs)& (inj f)&
                  (ALL x:cs.(EX y:cs. x=f y))&
            f d1=c1 & f d2=c2)" (is "EX f. ?P f")
proof(cut_tac M1 a0 M2 M3,rule permutation_exists ) qed auto

then obtain f where N2:"?P f" by blast


have "EX tr':traces' cs. length tr'=length tr &  state_permutating (last tr) (last tr') f cs" (is "EX tr':traces' cs.?Q tr'")
proof(cut_tac M5 N2,rule sym_cache_term,auto)qed
(*let ?permutation_f="\<lambda> f.(f c1=d1 & f d1=c1 & f c2=d2& f d2=c2 &( ~ x:{c1,d1,c2,d2}\<longrightarrow>f x=x)) "*)
then obtain tr' where N3:"tr':traces' cs &?Q tr'"  by blast

from N3  have N4:"cache (last tr) d1=cache (last tr') c1" apply - apply(cut_tac M2 N2, unfold state_permutating_def, (erule conjE)+)
apply(thin_tac " \<forall>x\<in>cs. \<exists>y\<in>cs. x = f y",drule_tac x="d1" in bspec,auto) done
from N3  have N5:"cache (last tr) d2=cache (last tr') c2"
apply - apply(cut_tac M3 N2, unfold state_permutating_def, (erule conjE)+)
apply(thin_tac " \<forall>x\<in>cs. \<exists>y\<in>cs. x = f y",drule_tac x="d2" in bspec,auto) done
from N4 N5  M4 a1 N3 show ?thesis   apply - apply(drule_tac x="tr'" in bspec) apply auto done
qed
qed

lemma sym_prop2:
assumes a0:"c1 ~= c2 & c1:cs&c2:cs" and 
        a1:"ALL tr:traces' cs.(
         channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
         cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack)" 
shows "
        (ALL tr c1 c2. (tr:traces' cs &c1 ~= c2 & c1:cs&c2:cs&
         channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
         cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack))"
proof((rule allI)+, rule impI,(erule conjE)+)
fix tr d1 d2
assume M1:"d1 \<noteq> d2" and M2:" d1 \<in> cs" and M3:" d2 \<in> cs" and
       M4:"channel3 (last tr) d1 = invalidate_ack" and M5:"tr \<in> traces' cs"
show "cache (last tr) d2 \<noteq> exclusive \<and> channel2_4 (last tr) d2 \<noteq> grant_exclusive \<and> channel3 (last tr) d2 \<noteq> invalidate_ack"
proof -
have N1:"
     EX f.((ALL x. x :(cs) \<longrightarrow>f x:cs)& (inj f)&
                  (ALL x:cs.(EX y:cs. x=f y))&
            f d1=c1 & f d2=c2)" (is "EX f. ?P f")
proof(cut_tac M1 a0 M2 M3,rule permutation_exists ) qed auto

then obtain f where N2:"?P f" by blast


have "EX tr':traces' cs. length tr'=length tr &  state_permutating (last tr) (last tr') f cs" (is "EX tr':traces' cs.?Q tr'")
proof(cut_tac M5 N2,rule sym_cache_term,auto)qed
(*let ?permutation_f="\<lambda> f.(f c1=d1 & f d1=c1 & f c2=d2& f d2=c2 &( ~ x:{c1,d1,c2,d2}\<longrightarrow>f x=x)) "*)
then obtain tr' where N3:"tr':traces' cs &?Q tr'"  by blast

from N3  have N4:"channel3 (last tr) d1=channel3 (last tr') c1" apply - apply(cut_tac M2 N2, unfold state_permutating_def, (erule conjE)+)
apply(thin_tac " \<forall>x\<in>cs. \<exists>y\<in>cs. x = f y",drule_tac x="d1" in bspec,auto) done
from N3  have N5:"cache (last tr) d2=cache (last tr') c2&channel2_4 (last tr) d2=channel2_4 (last tr') c2&
                channel3 (last tr) d2=channel3 (last tr') c2 "
apply - apply(cut_tac M3 N2, unfold state_permutating_def, (erule conjE)+)
apply(thin_tac " \<forall>x\<in>cs. \<exists>y\<in>cs. x = f y",drule_tac x="d2" in bspec,auto) done
from N4 N5  M4 a1 N3 show ?thesis   apply - apply(drule_tac x="tr'" in bspec) apply simp+  done
qed
qed

lemma cache_invariant_aux1:
assumes a0:"c1 ~= c2 & c1:cs&c2:cs" and
        
        a2:"c3:cs"  and
        a3:"~c1=c3"  and a4:"~c2=c3"    and
        a6:"ALL tr:(abs_traces1 {c1,c2} c3 ).((cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid) &
                                               (channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                                                 cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack))" 

shows "(ALL tr:traces' cs. ( c1 ~= c2 & c1:cs&c2:cs&cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid ))&
       (ALL tr:traces' cs.(c1 ~= c2 & c1:cs&c2:cs&channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                         cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack))"
   (is "(ALL tr:traces' cs . ?P1 tr )&(ALL tr:traces' cs. ?P2 tr )")
proof(rule conjI)
show "(ALL tr:traces' cs.  ?P1 tr )"
proof( rule  ballI, rule  impI)
fix tr
assume  M1:"tr \<in> traces' cs" and M2:" c1 \<noteq> c2 \<and> c1 \<in> cs \<and> c2 \<in> cs \<and> cache (last tr) c1 = exclusive"
show "cache (last tr) c2 = invalid"
thm three_sim_any
proof -
have "\<exists>tr'\<in>abs_traces1 {c1, c2} c3.
      state_sim_on (last tr) (last tr') {c1, c2} \<and>
      (home_current_command (last tr) = home_current_command (last tr') \<and>
       home_exclusive_granted (last tr) = home_exclusive_granted (last tr')) \<and>
      (home_current_command (last tr) \<noteq> empty_message \<and> home_current_client (last tr) \<in> cs - {c1, c2} \<longrightarrow>
       home_current_client (last tr') = c3) \<and>
      (home_current_command (last tr) \<noteq> empty_message \<and> home_current_client (last tr) \<in> {c1, c2} \<longrightarrow>
       home_current_client (last tr') = home_current_client (last tr))"
apply - apply(cut_tac a0  a2 a3 a4 M1,rule_tac cs="cs" and ?d1.0="c1" and ?d2.0="c2" in three_sim_any) apply simp+ done
then obtain tr' where N2:"tr'\<in>abs_traces1 {c1, c2} c3&
                          state_sim_on (last tr) (last tr') {c1, c2}" by blast
then have "cache (last tr) c1 = cache (last tr') c1 & cache (last tr) c2= cache (last tr') c2" 
apply - apply(unfold state_sim_on_def, auto) done

from a6 this N2  have "?P1 tr" 
proof(drule_tac x="tr'" in  bspec ,simp+) qed

with M2 M1 show ?thesis by simp 
qed
qed
next
show "ALL tr:traces' cs.?P2 tr"
proof(rule ballI, rule impI)
fix tr
assume  M1:"tr \<in> traces' cs" and M2:" c1 \<noteq> c2 \<and> c1 \<in> cs \<and> c2 \<in> cs \<and> channel3 (last tr) c1 = invalidate_ack"
show " cache (last tr) c2 \<noteq> exclusive \<and> channel2_4 (last tr) c2 \<noteq> grant_exclusive \<and> channel3 (last tr) c2 \<noteq> invalidate_ack"
thm three_sim_any
proof -
have "\<exists>tr'\<in>abs_traces1 {c1, c2} c3.
      state_sim_on (last tr) (last tr') {c1, c2} \<and>
      (home_current_command (last tr) = home_current_command (last tr') \<and>
       home_exclusive_granted (last tr) = home_exclusive_granted (last tr')) \<and>
      (home_current_command (last tr) \<noteq> empty_message \<and> home_current_client (last tr) \<in> cs - {c1, c2} \<longrightarrow>
       home_current_client (last tr') = c3) \<and>
      (home_current_command (last tr) \<noteq> empty_message \<and> home_current_client (last tr) \<in> {c1, c2} \<longrightarrow>
       home_current_client (last tr') = home_current_client (last tr))"
apply - apply(cut_tac a0  a2 a3 a4 M1,rule_tac cs="cs" and ?d1.0="c1" and ?d2.0="c2" in three_sim_any) apply simp+ done
then obtain tr' where N2:"tr'\<in>abs_traces1 {c1, c2} c3&
                          state_sim_on (last tr) (last tr') {c1, c2}" by blast
then have N3:"cache (last tr) c1 = cache (last tr') c1 & cache (last tr) c2= cache (last tr') c2&
           channel3 (last tr) c1= channel3 (last tr') c1 &
           channel2_4 (last tr) c2 = channel2_4 (last tr') c2 & channel3 (last tr) c2= channel3 (last tr') c2" 
apply - apply(unfold state_sim_on_def, auto) done

from a6 this M2  have "cache (last tr') c2 \<noteq> exclusive \<and> channel2_4 (last tr') c2 \<noteq> grant_exclusive \<and> channel3 (last tr') c2 \<noteq> invalidate_ack"
proof(drule_tac x="tr'" in  bspec ,cut_tac N2,simp, subgoal_tac "channel3 (last tr') c1 = invalidate_ack",simp+) qed

with M2 N3  show ?thesis by simp
qed
qed
qed

lemma cache_invariant_aux2:
assumes a0:"c1 ~= c2 & c1:cs&c2:cs" and
        
        a2:"c3:cs"  and
        a3:"~c1=c3"  and a4:"~c2=c3"    and
        a6:"ALL tr:(abs_traces1 {c1,c2} c3 ).((cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid) &
                                               (channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                                                 cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack))" 

shows "(ALL c1 c2. (ALL tr:traces' cs. ( c1 ~= c2 & c1:cs&c2:cs&cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid )))&
       (ALL c1 c2.(ALL tr:traces' cs.  (c1 ~= c2 & c1:cs&c2:cs&channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                         cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack)))"
   (is "(ALL c1 c2. (ALL tr:traces' cs. ?P1 tr c1 c2) )&(ALL c1 c2.(ALL tr:traces' cs. ?P2 tr c1 c2) )")
proof 

show "ALL c1 c2. (ALL tr:traces' cs. ?P1 tr c1 c2)"
proof-
have "(ALL tr:traces' cs. ( c1 ~= c2 & c1:cs&c2:cs&cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid ))&
       (ALL tr:traces' cs.(c1 ~= c2 & c1:cs&c2:cs&channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                         cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack))"
apply - apply(cut_tac a0  a2 a3 a4 a6 ,rule cache_invariant_aux1,  simp+)  done

then have "(ALL tr c1 c2. (tr:traces' cs &c1 ~= c2 & c1:cs&c2:cs&
         cache (last tr) c1 = exclusive)\<longrightarrow> cache (last tr) c2 = invalid)"
apply - apply(cut_tac a0  a2 a3 a4,rule_tac ?c1.0="c1" and ?c2.0="c2"  in sym_prop1)
        apply( simp+) done

then show ?thesis by blast

qed

next
show "ALL c1 c2. (ALL tr:traces' cs. ?P2 tr c1 c2)"

proof-
have "(ALL tr:traces' cs. ( c1 ~= c2 & c1:cs&c2:cs&cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid ))&
       (ALL tr:traces' cs.(c1 ~= c2 & c1:cs&c2:cs&channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                         cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack))"
apply - apply(cut_tac a0  a2 a3 a4 a6 ,rule cache_invariant_aux1,  simp+)  done

then have "(ALL tr c1 c2. (tr:traces' cs &c1 ~= c2 & c1:cs&c2:cs
         & channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
         cache (last tr) c2 \<noteq> exclusive \<and> channel2_4 (last tr) c2 \<noteq> grant_exclusive \<and> channel3 (last tr) c2 \<noteq> invalidate_ack))"
apply - apply(cut_tac a0  a2 a3 a4,rule_tac ?c1.0="c1" and ?c2.0="c2"  in sym_prop2)
        apply( simp+) done

then show ?thesis by blast

qed
qed

lemma cache_invariant_aux3:
assumes a0:"c1 ~= c2 & c1:cs&c2:cs" and
        
        a2:"c3:cs"  and
        a3:"~c1=c3"  and a4:"~c2=c3"    and
        a6:"ALL tr:(abs_traces1 {c1,c2} c3 ).((cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid) &
                                               (channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                                                 cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack))" 

shows "(ALL c1 c2. (ALL tr:traces cs. ( c1 ~= c2 & c1:cs&c2:cs&cache (last tr) c1 = exclusive\<longrightarrow> cache (last tr) c2 = invalid )))&
       (ALL c1 c2.(ALL tr:traces cs.  (c1 ~= c2 & c1:cs&c2:cs&channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
                         cache (last tr) c2~=exclusive & channel2_4 (last tr) c2~=grant_exclusive & channel3 (last tr) c2~=invalidate_ack)))"
   (is "(ALL c1 c2. (ALL tr:traces cs. ?P1 tr c1 c2) )&(ALL c1 c2.(ALL tr:traces cs. ?P2 tr c1 c2) )")
proof -
from a0  a2 a3 a4 a6 have M0: "(ALL c1 c2. (ALL tr:traces' cs. ?P1 tr c1 c2) )&(ALL c1 c2.(ALL tr:traces' cs. ?P2 tr c1 c2) )"
by (rule cache_invariant_aux2)

 show ?thesis
proof(rule conjI, (rule allI)+, rule ballI, rule impI,(erule conjE)+) 

thm trace_is_trace'
fix c1 c2 tr
assume M1:"tr \<in> traces cs" and  M2:"c1 \<noteq> c2"
       and M3:" c1 \<in> cs" and M4:" c2 \<in> cs" and M5:" cache (last tr) c1 = exclusive"
show "cache (last tr) c2 = invalid"
proof - 
from M1 M0 have "tr:traces' cs" 
apply - apply(rule trace_is_trace', unfold invariant2_def, simp)
apply(rule ballI) apply( rule ballI,rule impI) apply(rule ballI, rule impI)
apply(erule conjE)+ apply(rotate_tac -3) apply(drule_tac x="c" in spec)
apply(rotate_tac -1)
apply(drule_tac x="i" in spec)
apply(rotate_tac -1)
apply(drule_tac x="tr" in bspec)
apply (simp, subgoal_tac "c~=i", blast+)
done
from this M0 M1 M2 M3 M4 M5 show ?thesis by blast
qed
next
show " \<forall>c1 c2. \<forall>tr\<in>traces cs.
               c1 \<noteq> c2 \<and> c1 \<in> cs \<and> c2 \<in> cs \<and> channel3 (last tr) c1 = invalidate_ack \<longrightarrow>
               cache (last tr) c2 \<noteq> exclusive \<and> channel2_4 (last tr) c2 \<noteq> grant_exclusive \<and> channel3 (last tr) c2 \<noteq> invalidate_ack"
proof((rule allI)+, rule ballI,rule impI)
fix c1 c2 tr
assume M1:"tr \<in> traces cs" and  M2:"c1 \<noteq> c2 \<and> c1 \<in> cs \<and> c2 \<in> cs \<and> channel3 (last tr) c1 = invalidate_ack"
show "cache (last tr) c2 \<noteq> exclusive \<and> channel2_4 (last tr) c2 \<noteq> grant_exclusive \<and> channel3 (last tr) c2 \<noteq> invalidate_ack
"
proof - 
from M1 M0 have "tr:traces' cs" 
apply - apply(rule trace_is_trace', unfold invariant2_def, simp)
apply(rule ballI) apply( rule ballI,rule impI) apply(rule ballI, rule impI)
apply(erule conjE)+ apply(rotate_tac -3) apply(drule_tac x="c" in spec)
apply(rotate_tac -1)
apply(drule_tac x="i" in spec)
apply(rotate_tac -1)
apply(drule_tac x="tr" in bspec)
apply (simp, subgoal_tac "c~=i", blast+)
done
from this M0 M1 M2  show ?thesis by blast
qed
qed
qed
qed

end
